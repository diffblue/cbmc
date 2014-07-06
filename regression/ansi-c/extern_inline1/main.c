#ifdef __GNUC__
extern int foo(int);

extern inline int foo(int a)
{
  return 42;
}

int foo(int a)
{
  return 0;
}
#endif

int main()
{
}

