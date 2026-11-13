int main()
{
  float a = __VERIFIER_nondet_float(), b = __VERIFIER_nondet_float();
  __CPROVER_assert((a>b)==(a-b>0), "theorem");
}
