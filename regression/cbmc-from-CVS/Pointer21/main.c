struct A
{
  int i;
};

struct B
{
  int i;
  int j;
};

int func(struct A a)
{
  return a.i;
}

int main()
{
  struct B b;
  int x;

  b.i = 1;

  assert((* ((struct A*)&b)).i == 1); // This works fine.

  x=func( * ((struct A*)&b));
  assert(x == 1);
}
