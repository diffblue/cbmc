int main()
{
  double f1, _f1;
  f1=_f1;
  __CPROVER_assume(__CPROVER_isnormal(f1));
  assert(!__CPROVER_isnan(f1));
  assert(!__CPROVER_isinf(f1));
  assert(__CPROVER_isfinite(f1));

  double f2, _f2;
  f2=_f2;
  __CPROVER_assume(__CPROVER_isinf(f2));
  assert(!__CPROVER_isnormal(f2));
  assert(!__CPROVER_isnan(f2));

  double f3, _f3;
  f3=_f3;
  __CPROVER_assume(__CPROVER_isnan(f3));
  assert(!__CPROVER_isnormal(f3));
  assert(!__CPROVER_isinf(f3));
  assert(f3!=f3);

  double f4, _f4;
  f4=_f4;
  __CPROVER_assume(__CPROVER_isfinite(f4));
  assert(!__CPROVER_isnan(f4));
  assert(!__CPROVER_isinf(f4));

  double f5, _f5;
  f5=_f5;
  __CPROVER_assume(!__CPROVER_isnan(f5) && !__CPROVER_isinf(f5));
  assert(__CPROVER_isfinite(f5));
}
