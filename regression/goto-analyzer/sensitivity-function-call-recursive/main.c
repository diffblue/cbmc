#include <assert.h>

int bar(int other)
{
  if(other > 0)
  {
    int value = bar(other - 1);
    return value + 1;
  }
  else
  {
    return 0;
  }
}

int bar_clean(int other)
{
  if(other > 0)
  {
    int value = bar_clean(other - 1);
    return value + 1;
  }
  else
  {
    return 0;
  }
}

int fun(int changing, int constant)
{
  if(changing > 0)
  {
    int value = fun(changing - 1, constant);
    return value;
  }
  else
  {
    return constant;
  }
}

int main()
{
  int x=3;
  int y=bar(x+1);
  assert(y==4); // Unknown in the constants domain

  int y2 = bar(0);
  assert(y2==0); // Unknown since we are not sensitive to call domain

  int z = bar_clean(0);
  assert(z==0); // Unknown as the function has parameter as top

  int w = fun(5, 18);
  assert(w==18);
}
