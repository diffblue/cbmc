int main()
{
  char *p, *q, *r, *s, *t, *v;

#pragma CPROVER check push
#pragma CPROVER check enable "pointer-primitive"
  // must generate checks
  if(__CPROVER_r_ok(p, 1))
  {
  }
#pragma CPROVER check push
#pragma CPROVER check disable "pointer-primitive"
  // must not generate checks
  if(__CPROVER_r_ok(q, 1))
  {
  }
#pragma CPROVER check push
#pragma CPROVER check enable "pointer-primitive"
  // must generate checks
  if(__CPROVER_r_ok(r, 1))
  {
  }
#pragma CPROVER check pop
  // must not generate generate checks
  if(__CPROVER_r_ok(s, 1))
  {
  }
#pragma CPROVER check pop
  // must generate generate checks
  if(__CPROVER_r_ok(t, 1))
  {
  }
#pragma CPROVER check pop
  // must generate generate checks
  if(__CPROVER_r_ok(v, 1))
  {
  }
  return 0;
}
