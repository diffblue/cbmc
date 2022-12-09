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
__CPROVER_assigns(*l, *b) __CPROVER_ensures(is_list(*l, LIST_LEN))
__CPROVER_ensures(is_double_buffer(*b))
// clang-format on
{
  *l = create_node(1, create_node(2, create_node(3, NULL)));
  *b = create_double_buffer(1, 10);
}

void bar()
{
  list_t *l = NULL;
  double_buffer_t *b = NULL;

  foo(&l, &b);

  assert(__CPROVER_r_ok(l, sizeof(list_t)));
  assert(__CPROVER_r_ok(l->next, sizeof(list_t)));
  assert(__CPROVER_r_ok(l->next->next, sizeof(list_t)));
  assert(l->next->next->next == NULL);
  assert(MIN_VALUE <= l->value && l->value <= MAX_VALUE);
  assert(MIN_VALUE <= l->next->value && l->next->value <= MAX_VALUE);
  assert(
    MIN_VALUE <= l->next->next->value && l->next->next->value <= MAX_VALUE);
  assert(__CPROVER_r_ok(b, sizeof(double_buffer_t)));
  assert(__CPROVER_r_ok(b->first, sizeof(buffer_t)));
  assert(__CPROVER_r_ok(b->first->arr, b->first->size));
  assert(
    MIN_BUFFER_SIZE <= b->first->size && b->first->size <= MAX_BUFFER_SIZE);
  assert(__CPROVER_r_ok(b->second, sizeof(buffer_t)));
  assert(__CPROVER_r_ok(b->second->arr, b->second->size));
  assert(
    MIN_BUFFER_SIZE <= b->second->size && b->second->size <= MAX_BUFFER_SIZE);
}

int main()
{
  bar();
}
