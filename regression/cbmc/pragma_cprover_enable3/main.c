int main()
{
  char *p, *q;

#pragma CPROVER check push
#pragma CPROVER check enable "pointer-primitive"
  // generate checks for the following statements and fail
  if(__CPROVER_r_ok(p, 1))
  {
  }
#pragma CPROVER check pop

  // but do not generate checks on the following statements
  if(__CPROVER_r_ok(q, 1))
  {
  }
}
