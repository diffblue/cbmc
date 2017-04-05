#include <assert.h>

int main(int argc, char *argv[])
{
  // Test how well we can represent structs
  struct int_float
  {
	int a;
	float b;
  };
  struct int_float x={0, 1.0f};
  x.a=0;
  x.b=1.0f;
  assert(x.a==0);
  assert(x.a==1);

  // Test merging when there is only one value on both paths
  if(argc>2)
  {
    x.a=0;
    x.b=1.0f;
  }
  assert(x.a==0);

  // Test merging when there is one value for a and two values for b, to test if
  // we are representing them separately
  if(argc>3)
  {
    x.a=0;
    x.b=2.0f;
  }
  assert(x.a==0);
  assert(x.b>0.0f);
  assert(x.b==1.0f);

  // Test merging when there are two values for a and b
  if(argc>4)
  {
    x.a=1;
    x.b=2.0f;
  }
  assert(x.a<2);
  assert(x.a>2);
  assert(x.a==1);

  return 0;
}
