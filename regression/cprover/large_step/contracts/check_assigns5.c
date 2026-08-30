struct S
{
  int x, y;
};

void my_function1(struct S *s) __CPROVER_requires(__CPROVER_rw_ok(s))
  __CPROVER_assigns(*s) // passes
{
  s->x = 10;
  s->y = 10;
}

void my_function2(struct S *s) __CPROVER_requires(__CPROVER_rw_ok(s))
  __CPROVER_assigns(s->x) // passes
{
  s->x = 10;
}

void my_function3(struct S *s) __CPROVER_requires(__CPROVER_rw_ok(s))
  __CPROVER_assigns(s->y) // passes
{
  s->y = 10;
}

void my_function4(struct S *s) __CPROVER_requires(__CPROVER_rw_ok(s))
  __CPROVER_assigns(s->y) // fails
{
  s->x = 10;
}
