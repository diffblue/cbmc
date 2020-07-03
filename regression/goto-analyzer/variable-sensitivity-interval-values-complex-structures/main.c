#include <assert.h>
#include <stdio.h>

struct Vec2
{
  int x;
  int y;
};

void MakeZero(struct Vec2 *vec)
{
  vec->x = 0;
  vec->y = 0;
}

void MakeOne(struct Vec2 *vec)
{
  vec->x = 1;
  vec->y = 1;
}

int main(void)
{
  struct Vec2 vec = {-10, 10};
  struct Vec2 vecMinusTenAndTen = vec;
  int nondet_condition;
  if(nondet_condition)
  {
    MakeZero(&vec);
    struct Vec2 vecZero = vec;
  }
  else
  {
    MakeOne(&vec);
    struct Vec2 vecOne = vec;
  }
  struct Vec2 vecZeroOrOne = vec;
  vec.x = 13;
  vec.y = 42;
  struct Vec2 vecThirteenAndFourtyTwo = vec;
  return 0;
}
