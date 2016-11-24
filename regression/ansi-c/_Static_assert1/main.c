
// Not yet available in Visual Studio

#ifdef _MSC_VER

int main()
{
}

#else

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
