struct X {
  int y;
};

struct Y {
  struct X x;
};

int main()
{
  struct X nondet_X(void);
  struct X foo1 = nondet_X();
  struct Y foo2;

  foo2=(struct Y){ foo1 };

  assert(foo2.x.y==foo1.y);
}
