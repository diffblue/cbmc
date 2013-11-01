int main()
{
  double d, q, r;
  __CPROVER_assume(__CPROVER_isfinited(q));
  d=q;
  r=d+0;
  assert(r==d);
}
