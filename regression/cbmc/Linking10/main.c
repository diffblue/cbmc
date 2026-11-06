// TU1: struct A is incomplete, struct B is complete
struct A;
struct B
{
  int y;
};

void f(struct A *a, struct B *b);

int main()
{
  struct B b;
  b.y = 10;
  f((struct A *)0, &b);
  return 0;
}
