#include <stdio.h>

void set();

char buffer[10];

void init() {
  int i;
  for (i = 0; i < 10; i++) {buffer[i] = 0;}
}

void print() {
  printf("buffer = %s\n",buffer);
}

void main () {
  init();
  set();
  print();
}



