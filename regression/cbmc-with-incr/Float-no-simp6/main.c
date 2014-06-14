#include <assert.h>

void multiply(void)
{
	   /*
	   ((f1 == 0x1.000000p-63f) && (f2 == 0x1.fffffep-64f)) ||
	   ((f1 == 0x1.084c64p-63f) && (f2 == 0x1.efec9ep-64f)) ||
	   ((f1 == 0x1.47e8c2p-63f) && (f2 == 0x1.8fb86cp-64f)) ||
	   ((f1 == 0x1.1fcf1cp-63f) && (f2 == 0x1.c769c0p-64f)) ||
	   ((f1 == 0x1.b1fffcp-63f) && (f2 == 0x1.2e025ep-64f)) ||
	   ((f1 == 0x1.000000p-62f) && (f2 == 0x1.fffffep-65f)) ||
	   ((f1 == 0x1.000000p-61f) && (f2 == 0x1.fffffep-66f)) ||
	   ((f1 == 0x1.000000p-50f) && (f2 == 0x1.fffffep-77f)) ||
	   ((f1 == 0x1.000000p-30f) && (f2 == 0x1.fffffep-97f)) ||
	   ((f1 == 0x1.000000p-10f) && (f2 == 0x1.fffffep-117f)) ||
	   */

  float f1=0x1.000000p-1f;
  float f2=0x1.fffffep-126f;

  float res = f1 * f2;

  assert(res == 0x1.0p-126f);
}

void divide(void)
{
  float f1=0x1.000000p+1f;
  float f2=0x1.fffffep-126f;

  float res = f2 / f1;

  assert(res == 0x1.0p-126f);
}

void cast(void)
{
  double d = 0x1.fffffep-127;

  float f = (float)d;

  assert(f == 0x1.0p-126f);
}

int main()
{
  multiply();
  divide();
  cast();
}
