// The functions are called without a prototype in scope, so the arguments
// keep their own types. Symbolic execution reinterprets the enum argument
// and rejects the double argument; the inliner must not fail on either.
enum E
{
  A = 3
};

int as_int();
int from_double();

int main()
{
  enum E e = A;
  __CPROVER_assert(as_int(e) == 3, "enum argument reinterpreted");
  __CPROVER_assert(from_double(1.5) == 1, "double argument is nondet");
  return 0;
}

int as_int(int x)
{
  return x;
}

int from_double(int x)
{
  return x;
}
