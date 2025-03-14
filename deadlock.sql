create or replace function  random_string( int ) returns text as $$
select string_agg(substring('0123456789bcdfghjkmnpqrstvwxyz', ceil(random() * 30)::integer, 1), '') from generate_series(1, $1);
$$ language sql;

drop table if exists t1;
-- set fillfactor small for simplicity
create table if not exists t1 (a varchar) with (fillfactor =20);
-- we have 1 block = 1 range for simplicity

-- insert tuple, it will be the only tuple in the 1 range
insert into t1 (a) VALUES (random_string(2000));

-- insert tuple, it will be the only tuple in the 2 range
insert into t1 (a) VALUES (random_string(2000));

-- insert tuple. first tuple in the 3 range. it's small enough so next insert can put tuple in 3 range.
insert into t1 (a) VALUES (random_string(20));

create index t1_a_brin_idx on t1 using brin (a) with (pages_per_range = 1) ;

-- check you have 3 record as a result fo the query:
select * from brin_page_items(get_raw_page('t1_a_brin_idx',2),'t1_a_brin_idx');

-- insert leads to update of brin tuple for 3rd range, but new version of the brin tuple needs more space and current regular page doesn't have it so
-- this results in the brin tuple for 3 range being moved to another regular page and revmap entry for 3rd range being updated.
-- lock ordering in this case: reg page lock -> revmap page lock
insert into t1 (a) VALUES (random_string(2030));