#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv)
{
  char password[8] = {'s', 'e', 'c', 'r', 'e', 't', '!', '\0'};
  char buffer[16] = {
    '\0',
  };
  int tmp;
  int index = 0;

  printf("Enter your name: ");
  while((tmp = getchar()) != '\n')
  {
    buffer[index] = tmp;
    ++index;
  }

  printf("%s\n", buffer);

  return 0;
}
