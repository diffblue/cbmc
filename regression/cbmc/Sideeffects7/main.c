int foo()
{
  __CPROVER_assert(0, "");
}

int main()
{
  struct
  {
    int a : 2;
  } b;
  int c;
  short d;
  // this is to make sure the fix for the below assignment does not introduce a
  // new bug
  d |= b.a = c >= 0;

  // we previously weren't able to handle the below
  short a = (a ^= 0) || foo();
}
