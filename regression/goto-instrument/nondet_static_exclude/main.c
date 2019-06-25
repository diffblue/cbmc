#define NULL 0

struct aStruct
{
  int a;
  int b;
};

struct aStruct *test1 = NULL;

struct aStruct test2 = {.a = 5, .b = 2};
struct aStruct test3 = {.a = 1, .b = 4};
struct aStruct *test4 = &test3;
struct aStruct *test5 = &test2;

static int value = 7;

#include "main_1.h"
#include <assert.h>

int main(int argc, char **argv)
{
  assert(test1 == NULL);
  assert(test2.a == 5);
  assert(test3.a == 1);
  assert(test3.b == 4);
  assert(test4->a == 1);
  assert(test4->b == 4);

  assert(test5->a == 5);
  assert(test5->b == 2);

  assert(value == 7);

  setup();

  return 0;
}
