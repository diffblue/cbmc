#include <pthread.h>

int a = 0;
int b = 0;

void *setThread(void *param);
void *checkThread(void *param);

int main(int argc, char *argv[]) {
  int i=0;
  static int iCheck = 2;

  pthread_create(0, 0, &setThread, 0);

  i=0;
  if(i<iCheck)
    pthread_create(0, 0, &checkThread, 0);

  return 0;
}

void *setThread(void *param) {
  a = 1;
  b = -1;

  return 0;
}

void *checkThread(void *param) {
  if (! ((a == 0 && b == 0) || (a == 1 && b == -1))) {
    assert(0);
  }

  return 0;
}

