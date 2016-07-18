
void test1() {}
void test2() {}

int main()
{
  void (*f)(void);
  f = test1;
  f = test2;

  f();

  return 0;
}

