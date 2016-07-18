
void test1() {}
void test2() {}

int main()
{
  void (*f)(void);
  f = test1;
  f = test2;

  (f == test1 ? test1 : test2)();

  return 0;
}

