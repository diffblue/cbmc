
void *thread1(void *arg) { return 0; }
void *thread2(void *arg) { return 0; }
void *thread3(void *arg) { return 0; }

void func6(void *(*f)(void *), int i)
{

}

void func5(void *(*f)(void *))
{
  func6(f, 1);
}

void func4(int i, void *(*f)(void *))
{

}

void func3(void *(*f)(void *))
{

}

void func2(void *(*f)(void *), void *(*g)(void *), int i, void *(*h)(void *))
{
  func3(h);
}

void func1(void *(*f)(void *))
{
  func2(f, f, 3, thread3);
}

int main()
{
  func1(thread1);

  func4(0, thread1);
  func4(1, thread2);

  func5(thread1);
  func5(thread2);
  func5(thread3);

  return 0;
}

