// all classification

int main()
{
  double d1, _d1;
  d1=_d1;
  __CPROVER_assume(__CPROVER_isnormald(d1));
  assert(!__CPROVER_isnand(d1));
  assert(!__CPROVER_isinfd(d1));
  assert(__CPROVER_isfinited(d1));

  double d2, _d2;
  d2=_d2;
  __CPROVER_assume(__CPROVER_isinfd(d2));
  assert(!__CPROVER_isnormald(d2));
  assert(!__CPROVER_isnand(d2));

  double d3, _d3;
  d3=_d3;
  __CPROVER_assume(__CPROVER_isnand(d3));
  assert(!__CPROVER_isnormald(d3));
  assert(!__CPROVER_isinfd(d3));
  assert(d3!=d3);

  double d4, _d4;
  d4=_d4;
  __CPROVER_assume(__CPROVER_isfinited(d4));
  assert(!__CPROVER_isnand(d4));
  assert(!__CPROVER_isinfd(d4));

  double d5, _d5;
  d5=_d5;
  __CPROVER_assume(!__CPROVER_isnand(d5) && !__CPROVER_isinfd(d5));
  assert(__CPROVER_isfinited(d5));
}
