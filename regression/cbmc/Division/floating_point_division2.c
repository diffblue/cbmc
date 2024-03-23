#include <assert.h>
#include <math.h>

double nondet_double();

int main()
{
  double y = nondet_double();

  if(y == 0)
  {
    // we expect to catch this with --float-div-by-zero-check
    double x = 1.0 / y;
  }
}
