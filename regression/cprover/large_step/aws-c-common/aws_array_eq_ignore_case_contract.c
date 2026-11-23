// Function: aws_array_eq_ignore_case
// Source: aws-c-common/source/byte_buf.c

#include <aws/common/byte_buf.h>

// bool aws_array_eq_ignore_case(
//    const void *const array_a,
//    const size_t len_a,
//    const void *const array_b,
//    const size_t len_b)

int main()
{
  const void *array_a, *array_b;
  size_t len_a, len_b;

  __CPROVER_assume(__CPROVER_r_ok(array_a, len_a));
  __CPROVER_assume(__CPROVER_r_ok(array_b, len_b));

  aws_array_eq_ignore_case(array_a, len_a, array_b, len_b);

  return 0;
}
