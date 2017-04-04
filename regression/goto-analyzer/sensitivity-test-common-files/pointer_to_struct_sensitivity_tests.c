#include <assert.h>

int main(int argc, char *argv[])
{
  // Test how well we can represent pointers to structs
  struct int_float
  {
	int a;
	float b;
  };
  struct int_float x={0, 1.0};
  x.a=0;
  x.b=1.0;
  struct int_float *p=&x;
  assert((*p).a==0);
  assert((*p).a==1);

  // Test alternative syntax
  assert(p->a==0);
  assert(p->a==1);

  // Test writing to the struct through the pointer
  p->b=2.0;
  assert(p->b==2.0);
  assert(p->b==1.0);

  return 0;
}
