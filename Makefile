MODULES = updatable_views

REGRESS = setup view_update view_not_updatable

PG_CONFIG = pg_config
PGXS = $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
