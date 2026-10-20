enum E
{
  A = -1,
  B = 1
};
enum E nondet_enum(void);

int main(void)
{
  enum E e = nondet_enum();
  __CPROVER_assume(e == A || e == B);
  long long l = e;
  // A signed enum converted to a wider integer must be sign-extended.
  __CPROVER_assert(l < 0 || l == 1, "sign-extended enum value is -1 or 1");
  return 0;
}
