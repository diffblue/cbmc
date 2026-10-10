struct S
{
  int a, b, c;
} x;

__CPROVER_size_t i = 3;

int array[10];

int main()
{
  x.a = 123;
  x.b = x.a;
  array[1] = 10;
  array[2] = 20;
  array[i] = 30;
  __CPROVER_assert(0, "property 1");
}
