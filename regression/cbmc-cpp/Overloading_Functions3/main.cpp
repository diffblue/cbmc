#include <assert.h>

// these are _different_

int f(char)
{
  return 1;
}

int f(unsigned char)
{
  return 2;
}

int f(short int)
{
  return 3;
}

int f(int)
{
  return 4;
}

int f(unsigned int)
{
  return 5;
}

int f(long int)
{
  return 6;
}

// not the same as long int
int f(long long)
{
  return 7;
}

int f(float)
{
  return 8;
}

int f(double)
{
  return 9;
}

// not the same as double!
int f(long double)
{
  return 10;
}

int main()
{
  assert(f((char)0)==1);
  assert(f((unsigned char)0)==2);
  assert(f((short int)0)==3);
  assert(f((int)0)==4);
  assert(f((unsigned int)0)==5);
  assert(f((long int)0)==6);
  assert(f((long long)0)==7);
  assert(f((float)0)==8);
  assert(f((double)0)==9);
  assert(f((long double)0)==10);
}
