#include <assert.h>

int main()
{
  int i, j=20;

  if(i>=20)
    assert(i>=10); // success

  if(i>=10 && i<=20)
    assert(i!=30); // success

  if(i>=10 && i<=20)
    assert(i!=15); // fails

  if(i<1 && i>10)
    assert(0); // success

  if(i>=10 && j>=i)
    assert(j>=10); // success

  if(i>=j)
    assert(i>=j); // unknown

  if(i>10)
    assert(i>=11); // success

  if(i<=100 && j<i)
    assert(j<100); // success
}
