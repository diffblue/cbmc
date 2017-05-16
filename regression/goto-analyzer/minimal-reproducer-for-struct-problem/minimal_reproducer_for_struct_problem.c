#include <assert.h>

int main(int argc, char *argv[])
{
  // Test if we can represent constant structs
  struct int_struct
  {
	int a;
  };

  struct int_struct x = {0};
  x.a = 0;
  assert(x.a==0);
  assert(x.a==1);

  if(argc>2)
  {
    assert(x.a==0);
    assert(x.a==1);
    x.a=1;
    assert(x.a==0);
    assert(x.a==1);
  }
  assert(x.a==0);
  assert(x.a==1);

  return 0;
}
