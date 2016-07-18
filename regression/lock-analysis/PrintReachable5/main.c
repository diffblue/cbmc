#include <stdlib.h>

void *thread1(void *arg) { return 0; }
void *thread2(void *arg) { return 0; }
void *thread3(void *arg) { return 0; }

void func3(void *(*f)(void *))
{

}

void func2(void *(*f)(void *), void *(*g)(void *), void *(*h)(void *))
{
  func3(0);
}

void func1(void *(*f)(void *))
{
  func2(f, NULL, thread3);
}

int main()
{
  func1(thread1);
  return 0;
}

