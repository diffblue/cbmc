// C++20 designated initializers
struct S
{
  int a;
  int b;
  int c;
};
int main()
{
  S s1{.a = 1, .b = 2, .c = 3};
  __CPROVER_assert(s1.a == 1, "designated a");
  __CPROVER_assert(s1.c == 3, "designated c");

  S s2{.a = 10, .c = 30};
  __CPROVER_assert(s2.a == 10, "skip b: a");
  __CPROVER_assert(s2.c == 30, "skip b: c");
  return 0;
}
