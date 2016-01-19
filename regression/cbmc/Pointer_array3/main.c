#include <assert.h>

int foo(int * A[])
{
  int * _A=A[0];
  return _A[1];
}

int main()
{
  int Y[2]={42, 13};
  int * A[1]={ 0 }; // should be Y instead of 0 for assertion to hold
  int x=foo(A);
  assert(x==13);
  return x;
}
