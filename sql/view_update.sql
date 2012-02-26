CREATE TABLE foo (a int, b text);

INSERT INTO foo VALUES (1, 'one');

CREATE VIEW foov1 AS SELECT a AS x, b AS y FROM foo WHERE a < 100;

CREATE TRIGGER foov1_update INSTEAD OF INSERT OR UPDATE OR DELETE ON foov1 FOR EACH ROW EXECUTE PROCEDURE update_view();

INSERT INTO foov1 VALUES (2, 'two');

SELECT * FROM foo;
SELECT * FROM foov1;
