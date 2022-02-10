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
  __CPROVER_assert(
    globalUnion.non_const == 10, "assertion globalUnion.non_const == 10");
  __CPROVER_assert(
    globalUnion.is_const == 10, "assertion globalUnion.is_const == 10");
  __CPROVER_assert(
    paramUnion.non_const == 20, "assertion paramUnion.non_const == 20");
  __CPROVER_assert(
    paramUnion.is_const == 20, "assertion paramUnion.is_const == 20");
  havoc_union(&paramUnion);
  __CPROVER_assert(
    globalUnion.non_const == 10, "assertion globalUnion.non_const == 10");
  __CPROVER_assert(
    globalUnion.is_const == 10, "assertion globalUnion.is_const == 10");
  __CPROVER_assert(
    paramUnion.non_const == 20, "assertion paramUnion.non_const == 20");
  __CPROVER_assert(
    paramUnion.is_const == 20, "assertion paramUnion.is_const == 20");
}
