#include <assert.h>

union WithConstMember {
  int non_const;
  const int is_const;
};

union WithConstMember globalUnion;
void havoc_union(union WithConstMember *u);

int main(void)
{
  union WithConstMember paramUnion;
  globalUnion.non_const = 10;
  paramUnion.non_const = 20;
  assert(globalUnion.non_const == 10);
  assert(globalUnion.is_const == 10);
  assert(paramUnion.non_const == 20);
  assert(paramUnion.is_const == 20);
  havoc_union(&paramUnion);
  assert(globalUnion.non_const == 10);
  assert(globalUnion.is_const == 10);
  assert(paramUnion.non_const == 20);
  assert(paramUnion.is_const == 20);
}
