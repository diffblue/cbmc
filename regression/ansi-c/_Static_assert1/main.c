struct S
{
  // Visual Studio does not support _Static_assert in compound bodies.
#ifndef _MSC_VER
  _Static_assert(1, "in struct");
#endif
  int x;
} asd;

_Static_assert(1, "global scope");

int main()
{
  _Static_assert(1, "in function");
}
