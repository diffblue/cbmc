#include <stdbool.h>
#include <stdlib.h>

typedef struct list_t
{
  int value;
  struct list_t *next;
} list_t;

#define MIN_VALUE -10
#define MAX_VALUE 10

bool is_list(list_t *l, size_t len)
{
  if(len == 0)
    return l == NULL;
  else
    return __CPROVER_is_fresh(l, sizeof(*l)) &&
           (MIN_VALUE <= l->value && l->value <= MAX_VALUE) &&
           is_list(l->next, len - 1);
}

typedef struct buffer_t
{
  size_t size;
  char *arr;
} buffer_t;

typedef struct double_buffer_t
{
  buffer_t *first;
  buffer_t *second;
} double_buffer_t;

#define MIN_BUFFER_SIZE 1
#define MAX_BUFFER_SIZE 10

bool is_sized_array(char *arr, size_t size)
{
  return (MIN_BUFFER_SIZE <= size && size <= MAX_BUFFER_SIZE) &&
         __CPROVER_is_fresh(arr, size);
}

bool is_buffer(buffer_t *b)
{
  return __CPROVER_is_fresh(b, sizeof(*b)) && is_sized_array(b->arr, b->size);
}

bool is_double_buffer(double_buffer_t *b)
{
  return __CPROVER_is_fresh(b, sizeof(*b)) && is_buffer(b->first) &&
         is_buffer(b->second);
}

#define LIST_LEN 3

int foo(list_t *l, double_buffer_t *b)
  // clang-format off
  __CPROVER_requires(is_list(l, LIST_LEN))
  __CPROVER_requires(is_double_buffer(b))
  __CPROVER_ensures(
      (2 * MIN_BUFFER_SIZE + LIST_LEN * MIN_VALUE) <= __CPROVER_return_value &&
      __CPROVER_return_value <= (2 * MAX_BUFFER_SIZE + LIST_LEN * MAX_VALUE))
// clang-format on
{
  // access the assumed data structure
  return l->value + l->next->value + l->next->next->value + b->first->size +
         b->second->size;
}

int main()
{
  list_t *l;
  double_buffer_t *b;
  int return_value = foo(l, b);
}
