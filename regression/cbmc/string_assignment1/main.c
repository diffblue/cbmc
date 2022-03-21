typedef char array_t[2][2];

void foo(array_t(*a))
{
  unsigned char i = 0;
  unsigned char j = 0;
  (*a)[i][j] = 0;
}

unsigned char main()
{
  char *x = "abcd";
  foo(x);
  __CPROVER_assert(x[0] == 'a', "a");
}
