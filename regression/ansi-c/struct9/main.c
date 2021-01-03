enum values
{
  A = 1,
  B = 2
};

struct S
{
  enum values v;
};

void foo()
{
  return;
}

void *bar()
{
  return 0;
}

int main()
{
  _Bool b;
  struct S s = b ? ((struct S){A}) : ((struct S){B});

  b ? foo() : bar();
}
