
int x;
int y;

int z;

int a[10];

typedef struct some_struct {
  int a;
  int b;
} some_struct_t;

some_struct_t s1;
some_struct_t s2;

void func1()
{
  s1.a = 7;
}

void func2()
{
  s2.a = 7;
}

void func3()
{
  func3();
}

int main()
{
  z = 1;
  z = a[0];

  func2();

  func3();

  return 0;
}
