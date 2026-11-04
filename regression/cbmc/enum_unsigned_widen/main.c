enum E
{
  A = 0x80000000u,
  B = 1
};
enum __attribute__((packed)) P
{
  X = 200,
  Y = 1
};
enum E nondet_e(void);
enum P nondet_p(void);

int main(void)
{
  // enum E has underlying type unsigned int
  enum E e = nondet_e();
  __CPROVER_assume(e == A || e == B);
  long long l = e;
  __CPROVER_assert(l > 0, "unsigned enum widened is positive");

  // enum P has underlying type unsigned char
  enum P p = nondet_p();
  __CPROVER_assume(p == X);
  int i = p;
  __CPROVER_assert(i == 200, "packed unsigned enum converts correctly");
  return 0;
}
