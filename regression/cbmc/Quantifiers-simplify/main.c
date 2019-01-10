int main()
{
  __CPROVER_assert(
    !__CPROVER_forall {
      int i;
      i >= 0
    },
    "simplify");

  return 0;
}
