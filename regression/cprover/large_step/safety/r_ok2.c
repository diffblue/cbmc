void int_assignment(int *p) __CPROVER_requires(__CPROVER_r_ok(p))
{
  *p; // safe

  int i = 123; // unrelated assignment

  *p; // still safe
}

void int_pointer_assignment(int *p) __CPROVER_requires(__CPROVER_r_ok(p))
{
  *p; // safe

  int *q = p; // unrelated assignment

  *p; // still safe
}

void pointer_assignment(int *p) __CPROVER_requires(__CPROVER_r_ok(p))
{
  *p; // safe

  p = 0; // wreck it

  *p; // not safe
}
