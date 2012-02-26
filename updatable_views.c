#include "postgres.h"
#include "fmgr.h"
#include "catalog/namespace.h"
#include "catalog/pg_type.h"
#include "commands/trigger.h"
#include "executor/spi.h"
#include "parser/parsetree.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"


PG_MODULE_MAGIC;

Datum update_view(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(update_view);


static Query *
get_view_query(Oid relid)
{
	static SPIPlanPtr saved_plan = NULL;
	Datum		args[1];
	char		nulls[1];
	int			spirc;
	HeapTuple	htup;
	TupleDesc	tupdesc;
	int			fno;
	char	   *ev_action;
	List	   *actions;
	Query	   *action;
	MemoryContext outercontext = CurrentMemoryContext;

	if (SPI_connect() != SPI_OK_CONNECT)
		elog(ERROR, "SPI_connect failed");

	if (!saved_plan)
	{
		static const char *query_getviewrule = "SELECT ev_action FROM pg_catalog.pg_rewrite WHERE rulename = '_RETURN' AND ev_class = $1";
		Oid			argtypes[1];
		SPIPlanPtr	plan;

		argtypes[0] = OIDOID;
		plan = SPI_prepare(query_getviewrule, 1, argtypes);
		if (plan == NULL)
			elog(ERROR, "SPI_prepare failed for \"%s\"", query_getviewrule);
		SPI_keepplan(plan);
		saved_plan = plan;
	}

	args[0] = ObjectIdGetDatum(relid);
	nulls[0] = ' ';
	spirc = SPI_execute_plan(saved_plan, args, nulls, true, 1);
	if (spirc != SPI_OK_SELECT)
		elog(ERROR, "failed to get pg_rewrite tuple for view %u", relid);
	if (SPI_processed != 1)
		elog(ERROR, "did not find rewrite tuple for view %u", relid);

	htup = SPI_tuptable->vals[0];
	tupdesc = SPI_tuptable->tupdesc;

	fno = SPI_fnumber(tupdesc, "ev_action");
	ev_action = MemoryContextStrdup(outercontext, SPI_getvalue(htup, tupdesc, fno));

	SPI_finish();

	actions = (List *) stringToNode(ev_action);
	action = linitial(actions);

	return action;
}


static void
check_view_updatable(Query *viewquery)
{
	ListCell   *lc;
	Bitmapset  *seen_cols;
	int			rtindex = 0;

	if (viewquery->distinctClause)
		elog(ERROR, "not updatable because of DISTINCT");

	if (viewquery->groupClause)
		elog(ERROR, "not updatable because of GROUP BY");

	if (viewquery->havingQual)
		elog(ERROR, "not updatable because of HAVING");

	if (viewquery->setOperations)
		elog(ERROR, "not updatable because of set operation");

	if (list_length(viewquery->jointree->fromlist) != 1)
		elog(ERROR, "not updatable because of more than FROM list item");
	else
	{
		Node   *n = linitial(viewquery->jointree->fromlist);
		RangeTblEntry *rte;

		if (!IsA(n, RangeTblRef))
			elog(ERROR, "not updatable because of non-plain FROM list item");

		rtindex = ((RangeTblRef *) n)->rtindex;
		rte = rt_fetch(rtindex, viewquery->rtable);
		if (rte->rtekind != RTE_RELATION)
			elog(ERROR, "not updatable because of non-table FROM item");
	}

	// TODO: no subselects in WHERE referencing upper relations

	if (viewquery->limitOffset)
		elog(ERROR, "not updatable because of OFFSET");

	if (viewquery->limitCount)
		elog(ERROR, "not updatable because of LIMIT");

	seen_cols = NULL;
	foreach (lc, viewquery->targetList)
	{
		TargetEntry	*te;
		Var	   *var;

		te = (TargetEntry *) lfirst(lc);

		if (!IsA(te->expr, Var))
			elog(ERROR, "not updatable because column %d is not a plain column reference", te->resno);

		var = (Var *) te->expr;
		if (var->varno != rtindex)
			elog(ERROR, "variable references unknown range table entry");
		if (var->varattno == 0)
			elog(ERROR, "zero varattno not supported");
		if (bms_is_member(var->varattno, seen_cols))
			elog(ERROR, "not updatable because column %d of base table referenced multiple times", var->varattno);
		seen_cols = bms_add_member(seen_cols, var->varattno);
	}
}


/*
 * copied from dblink.c
 *
 * generate_relation_name - copied from ruleutils.c
 *      Compute the name to display for a relation
 *
 * The result includes all necessary quoting and schema-prefixing.
 */
static char *
generate_relation_name(Relation rel)
{
	char	   *nspname;
	char	   *result;

	/* Qualify the name if not visible in search path */
	if (RelationIsVisible(RelationGetRelid(rel)))
		nspname = NULL;
	else
		nspname = get_namespace_name(rel->rd_rel->relnamespace);

	result = quote_qualified_identifier(nspname, RelationGetRelationName(rel));

	return result;
}


static void
do_insert(Relation viewrel, Query *viewquery, HeapTuple newtuple)
{
	StringInfoData buf;
	StringInfoData buf2;
	ListCell   *lc;
	int			natts;
	int			i;
	SPIPlanPtr	plan;
	Oid		   *typeoids;
	Datum	   *values;
	char	   *nulls;
	Node	   *n;
	int			rtindex;
	Oid			baserelid;
	Relation	baserel;
	int			spirc;

	initStringInfo(&buf);
	initStringInfo(&buf2);

	n = linitial(viewquery->jointree->fromlist);
	Assert(IsA(n, RangeTblRef));
	rtindex = ((RangeTblRef *) n)->rtindex;
	baserelid = getrelid(rtindex, viewquery->rtable);
	baserel = heap_open(baserelid, AccessShareLock);

	appendStringInfo(&buf, "INSERT INTO %s (", generate_relation_name(baserel));

	natts = viewrel->rd_att->natts;
	typeoids = palloc(natts * sizeof(*typeoids));
	values = palloc(natts * sizeof(*values));
	nulls = palloc(natts * sizeof(*nulls));

	i = 0;
	foreach (lc, viewquery->targetList)
	{
		TargetEntry	*te;
		Var	   *var;
		char   *attname;

		te = (TargetEntry *) lfirst(lc);

		if (i > 0)
		{
			appendStringInfoString(&buf, ", ");
			appendStringInfoString(&buf2, ", ");
		}

		if (!IsA(te->expr, Var))
			elog(ERROR, "not a plain column reference");

		var = (Var *) te->expr;
		if (var->varno != rtindex)
			elog(ERROR, "rtindex mismatch");

		attname = get_rte_attribute_name(rt_fetch(var->varno, viewquery->rtable), var->varattno);
		appendStringInfo(&buf, "%s", quote_identifier(attname));
		appendStringInfo(&buf2, "$%d", i + 1);
		typeoids[i] = var->vartype;

		i++;
	}

	appendStringInfo(&buf, ") VALUES (");
	appendStringInfoString(&buf, buf2.data);
	appendStringInfo(&buf, ");");

	elog(NOTICE, "do_insert = %s", buf.data);

	SPI_connect();

	plan = SPI_prepare(buf.data, natts, typeoids);
	if (!plan)
		elog(ERROR, "prepare return = %d", SPI_result);
	// TODO: save plan in trigger context

	for (i = 0; i < natts; i++)
	{
		bool	isnull;

		values[i] = heap_getattr(newtuple, i + 1, viewrel->rd_att, &isnull);
		nulls[i] = isnull ? 'n' : ' ';
	}

	spirc = SPI_execute_plan(plan, values, nulls, false, 1);
	if (spirc != SPI_OK_INSERT)
		elog(ERROR, "spirc = %d", spirc);

	heap_close(baserel, AccessShareLock);

	SPI_finish();
}


Datum
update_view(PG_FUNCTION_ARGS)
{
	TriggerData *tdata;
	Query	   *viewquery;

	if (!CALLED_AS_TRIGGER(fcinfo))
		elog(ERROR, "not called as trigger");

	tdata = (TriggerData *) fcinfo->context;

	if (!TRIGGER_FIRED_INSTEAD(tdata->tg_event))
		elog(ERROR, "not called INSTEAD");

	if (!TRIGGER_FIRED_FOR_ROW(tdata->tg_event))
		elog(ERROR, "not called FOR ROW");

	viewquery = get_view_query(tdata->tg_relation->rd_id);
	check_view_updatable(viewquery);

	if (TRIGGER_FIRED_BY_INSERT(tdata->tg_event))
	{
		elog(NOTICE, "view INSERT");
		do_insert(tdata->tg_relation, viewquery, tdata->tg_trigtuple);
		return PointerGetDatum(tdata->tg_trigtuple);
	}
	else if (TRIGGER_FIRED_BY_DELETE(tdata->tg_event))
	{
		elog(NOTICE, "view DELETE");
		return PointerGetDatum(tdata->tg_trigtuple);
	}
	else if (TRIGGER_FIRED_BY_UPDATE(tdata->tg_event))
	{
		elog(NOTICE, "view UPDATE");
		return PointerGetDatum(tdata->tg_newtuple);
	}
	else
		elog(ERROR, "invalid trigger action");

	return PointerGetDatum(NULL);
}
