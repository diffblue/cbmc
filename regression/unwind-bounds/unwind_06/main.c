
const int a = 3;

void func(int n)
{
  int i;

  for (i = 0; i < n; i++) {} // func.0: 2
}

int main()
{
  int i;

  for(i = 0; i < a; i++) {} // main.0: 3

  int a[1];
  a[0]=4;

  for(i = 0; i < a[0]; i++) {} // main.1: 4

  typedef struct Test {
    int a;
  } test_t;

  test_t test;
  test.a = 5;

  for(i = 0; i < test.a; i++) {} // main.2: 5

  func(2);
}

