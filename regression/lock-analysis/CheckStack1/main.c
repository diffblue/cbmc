#include <pthread.h>

void func2()
{

}

void *thread(void *arg)
{
  int i;
  for (i = 0; i < 10; i++)
  {
    func2(); // 6
  }
}

void func1()
{
  pthread_t tid;
  pthread_create(&tid, 0, thread, 0); // 30
}

int main()
{
  func1(); // 0
  return 0;
}

