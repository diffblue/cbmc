#line 1 "test.c"

__inline int foo()
{
  return 0;
}

__forceinline int foo()
{
  return 1;
}

int main()
{
}
