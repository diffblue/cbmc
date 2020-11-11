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
  __CPROVER_assert((*p).a == 0, "(*p).a==0");
  __CPROVER_assert((*p).a == 1, "(*p).a==1");

  // Test alternative syntax
  __CPROVER_assert(p->a == 0, "p->a==0");
  __CPROVER_assert(p->a == 1, "p->a==1");

  // Test writing to the struct through the pointer
  p->b=2.0;
  __CPROVER_assert(p->b == 2.0, "p->b==2.0");
  __CPROVER_assert(p->b == 1.0, "p->b==1.0");

  // pointers to components
  int *comp_p = &x.a;
  __CPROVER_assert(comp_p == &x.a, "comp_p==&x.a");
  __CPROVER_assert(comp_p == &x.b, "comp_p==&x.b");
  __CPROVER_assert(*comp_p == 0, "*comp_p==0");
  __CPROVER_assert(*comp_p == 1, "*comp_p==1");

  float *compb_p = &x.b;
  __CPROVER_assert(compb_p == &x.a, "compb_p==&x.a");
  __CPROVER_assert(compb_p == &x.b, "compb_p==&x.b");
  __CPROVER_assert(*compb_p == 2.0, "*compb_p==2.0");
  __CPROVER_assert(*compb_p == 1.0, "*compb_p==1.0");

  // Use pointer implicitly pointing at the first component
  int *implicit_p = &x;
  __CPROVER_assert(implicit_p == &x.a, "implicit_p==&x.a");
  __CPROVER_assert(implicit_p == &x, "implicit_p==&x");
  __CPROVER_assert(*implicit_p == 0, "*implicit_p==0");
  __CPROVER_assert(*implicit_p == 1, "*implicit_p==1");

  // Write through pointer implicitly pointing at the first component
  *implicit_p = 5;
  __CPROVER_assert(x.a == 5, "x.a==5");
  __CPROVER_assert(x.a == 1, "x.a==1");

  return 0;
}
