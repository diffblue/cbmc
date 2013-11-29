#include <stdio.h>

int main() {
  int *p;
  int a=3;

  p=&a;
  printf("Value of integer pointed by p: %d\n",*p);
  p++;
  printf("Next value of integer pointed by p: %d\n",*p);
}
