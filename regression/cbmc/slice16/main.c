/* running example extracted from 
"In Slicing Programs with Jump Statements" 
by Hiralal Afrawal */
#include <assert.h>
int x;
_Bool nondet_bool();
unsigned int nondet_uint();

_Bool leof() {
  return nondet_bool();
}

int f1(int x) {
  return x*1;
}

int f2(int x) {
  return x*2;
}

int f3(int x) {
  return x*3;
}

void read(int *x) {
  x = nondet_uint();
}

int main() {
  int sum=0;
  int positives=0;
  while(leof())
  {
    read(x);
    if (x <= 0)  
      sum = sum + f1(x);
    else
    {
      positives = positives + 1;
      if (x%2 == 0)
        sum = sum + f2(x);
      else
        sum = sum + f3(x);
    }
  }
  assert(sum>=0);
  assert(positives>=0);
}
