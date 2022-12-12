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

list_t *create_node(int value, list_t *next)
{
  assert(MIN_VALUE <= value && value <= MAX_VALUE);
  list_t *result = malloc(sizeof(list_t));
  result->value = value;
  result->next = next;
  return result;
}

buffer_t *create_buffer(size_t size)
{
  assert(MIN_BUFFER_SIZE <= size && size <= MAX_BUFFER_SIZE);
  buffer_t *result = malloc(sizeof(buffer_t));
  result->arr = malloc(size);
  result->size = size;
  return result;
}

double_buffer_t *create_double_buffer(size_t first_size, size_t second_size)
{
  double_buffer_t *result = malloc(sizeof(double_buffer_t));
  result->first = create_buffer(first_size);
  result->second = create_buffer(second_size);
  return result;
}

void foo(list_t **l, double_buffer_t **b)
  // clang-format off
__CPROVER_requires(__CPROVER_is_fresh(l, sizeof(*l)))
__CPROVER_requires(__CPROVER_is_fresh(b, sizeof(*b)))
__CPROVER_assigns(*l, *b)
__CPROVER_ensures(is_list(*l, LIST_LEN))
__CPROVER_ensures(is_double_buffer(*b))
// clang-format on
{
  *l = create_node(1, create_node(2, create_node(3, NULL)));
  *b = create_double_buffer(1, 10);
}

int main()
{
  list_t *l;
  double_buffer_t *b;
  foo(&l, &b);
}
