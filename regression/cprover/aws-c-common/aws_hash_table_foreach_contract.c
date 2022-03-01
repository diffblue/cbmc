// Function: aws_hash_table_foreach
// Source: source/hash_table.c

#include <aws/common/hash_table.h>

// int aws_hash_table_foreach(
//   struct aws_hash_table *map,
//   int (*callback)(void *context, struct aws_hash_element *pElement),
//   void *context)

int main()
{
  struct aws_hash_table *map;
  int (*callback)(void *context, struct aws_hash_element *pElement);
  void *context;

  aws_hash_table_foreach(map, callback, context);

  return 0;
}
