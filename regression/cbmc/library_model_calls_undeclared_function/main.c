#include <assert.h>
#include <math.h>

// The model of copysign uses signbit, which include/math.h defines by
// unmodelled_signbit: a function that only the model declares and that has
// no model.  It must be in the goto program, as a function without a body;
// --validate-goto-model failed ("every function call callee must be in the
// function map").
int main()
{
  double r = copysign(1.0, -0.0);
  assert(r == 1.0 || r == -1.0);
  assert(r == -1.0);
  return 0;
}
