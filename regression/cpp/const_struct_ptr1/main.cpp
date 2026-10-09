struct A
{
  int x;
};

struct B
{
  const A *p;
};

void f(B &b, const A &a)
{
  b.p = &a;
}

int main()
{
  return 0;
}
