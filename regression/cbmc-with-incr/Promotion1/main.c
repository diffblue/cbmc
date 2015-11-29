#include <assert.h>

int main()
{
  // the result of promotion of unsigned short int is
  // signed int if int is bigger!
  unsigned short int a1=1;
  signed int b1=-1;

  if(sizeof(short)<sizeof(int))
    assert(a1>b1);
  else
    assert(a1<b1);

  // the result of promotion of unsigned char is
  // signed int if int is bigger!
  unsigned char a2=1;
  signed char b2=-1;
  
  if(sizeof(char)<sizeof(int))
    assert(a2>b2);
  else
    assert(a2<b2);  

  // the result of the arithmetic conversions is unsigned!
  unsigned int a3=1;
  signed int b3=-1;
  assert(a3<b3);

  // also true for long long.
  unsigned long long int a4=1;
  long long signed int b4=-1;
  assert(a4<b4);
}
