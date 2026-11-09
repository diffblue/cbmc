// Function: aws_hash_table_eq
// Source: source/hash_table.c

#include <aws/common/hash_table.h>

// bool aws_hash_table_eq(
//   const struct aws_hash_table *a,
//   const struct aws_hash_table *b,
//   aws_hash_callback_eq_fn *value_eq)

int main()
{
  const struct aws_hash_table *a;
  const struct aws_hash_table *b;
  aws_hash_callback_eq_fn *value_eq;

  aws_hash_table_eq(a, b, value_eq);

  return 0;
}
