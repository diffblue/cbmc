// C23 introduces the "static_assert" keyword.

struct S
{
  // Visual Studio does not support static_assert in compound bodies.
#ifndef _MSC_VER
  static_assert(1, "in struct");
#endif
  int x;
} asd;

static_assert(1, "global scope");

int main()
{
  static_assert(1, "in function");
}
