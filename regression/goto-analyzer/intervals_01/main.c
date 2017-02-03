#include <assert.h>

int main()
{
  int i, j=20;

  if(i>=20)
    assert(i>=10);

  if(i>=10 && i<=20)
    assert(i!=30);

  if(i>=10 && i<=20)
    assert(i!=15); // fails

  if(i<1 && i>10)
    assert(0);

  if(i>=10 && j>=i)
    assert(j>=10);

  if(i>=j)
    assert(i>=j); // fails

  if(i>10)
    assert(i>=11);

  if(i<=100 && j<i)
    assert(j<100);
}
