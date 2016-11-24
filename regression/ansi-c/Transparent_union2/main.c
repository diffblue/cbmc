// transparent union is GCC only
#ifdef __GNUC__
struct S
{
  int s;
};

typedef union
{
  struct S * sptr;
} U1 __attribute__((transparent_union));

typedef union
{
  const void * vptr;
} U2 __attribute__((transparent_union));

void foo1(U1 u)
{
  (void)u;
}

void foo2(U2 u)
{
  (void)u;
}

int main()
{
  int x;
  const void * v=&x;

  foo1(v);
  foo2(&x);

  return 0;
}
#else

int main()
{
}

#endif
