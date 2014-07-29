#ifdef __GNUC__
extern int foo(int);

extern inline int foo(int a)
{
  return 42;
}

// this is not allowed with C99 or above
int foo(int a)
{
  return 0;
}
#endif

int main()
{
}

