#include <stdarg.h>
#include <assert.h>

// how to do it:
// once an ellipsis is seen in the called function, declare an array of
// appropriate size (sum of sizeofs+paddings) and pass the array to the called
// function
// function with ellipsis has ellipsis replaced by void* pointer
// use of va_list is turned into assignment of this pointer
// va_start is no-op, just like va_end
// va_arg returns casted memory at pointer and increments pointer afterwards by
// given size (+padding)

int add_em_up (int count,...)
{
  va_list ap;
  int i, sum;

  va_start (ap, count);         /* Initialize the argument list. */

  sum = 0;
  for (i = 0; i < count; i++)
    sum += va_arg (ap, int);    /* Get the next argument value. */

  va_end (ap);                  /* Clean up. */
  return sum;
}

int main (void)
{
  /* This call prints 16. */
  assert(16 == add_em_up (3, 5, 5, 6));

  /* This call prints 55. */
  assert(55 == add_em_up (10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10));

  return 0;
}
