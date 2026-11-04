int main()
{
  double d, q = __VERIFIER_nondet_double(), r;
  __CPROVER_assume(__CPROVER_isfinited(q));
  d=q;
  r=d+0;
  assert(r==d);
}
