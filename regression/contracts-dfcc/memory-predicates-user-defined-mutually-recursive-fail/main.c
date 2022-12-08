#include <stdbool.h>
#include <stdlib.h>

typedef struct list_t
{
  int value;
  struct list_t *next;
} list_t;

bool is_positive_list(list_t *l, size_t len)
{
  if(len == 0)
    return l == NULL;
  else
    return __CPROVER_is_fresh(l, sizeof(*l)) && (l->value >= 0) &&
           is_negative_list(l->next, len - 1);
}

bool is_negative_list(list_t *l, size_t len)
{
  if(len == 0)
    return l == NULL;
  else
    return __CPROVER_is_fresh(l, sizeof(*l)) && (l->value <= 0) &&
           is_positive_list(l->next, len - 1);
}

#define LIST_LEN 3

void foo(list_t *l)
  // clang-format off
  __CPROVER_requires(is_positive_list(l, LIST_LEN))
// clang-format on
{
  assert(l->value >= 0);
  assert(l->next->value <= 0);
  assert(l->next->next->value >= 0);
}

int main()
{
  list_t *l;
  foo(l);
}
