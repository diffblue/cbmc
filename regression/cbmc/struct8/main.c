struct X
{
  int a, b, c;
};

int main()
{
  int aa = __VERIFIER_nondet_int(), bb = __VERIFIER_nondet_int(),
      cc = __VERIFIER_nondet_int();

  struct X foo;

  foo=(struct X) { aa, bb, cc };

  assert(foo.a==aa);
  assert(foo.b==bb);
  assert(foo.c==cc);
}
