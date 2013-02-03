
// Not yet available in Visual Studio

#ifndef _MSC_VER

struct S
{
  _Static_assert(1, "in struct");
  int x;
} asd;

_Static_assert(1, "global scope");

int main()
{
  _Static_assert(1, "in function");
}

#endif
