
void *thread1(void *arg) { return 0; }
void *thread2(void *arg) { return 0; }

void func2(void *(*f)(void *))
{

}

void func1(void *(*f)(void *))
{
  func2(f);
}

int main()
{
  func1(thread1);
  func1(thread2);

  return 0;
}

