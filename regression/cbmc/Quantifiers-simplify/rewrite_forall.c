int main()
{
  // clang-format off
  __CPROVER_assert(
    __CPROVER_forall {
      int i;
      // clang-format would rewrite the "==>" as "== >"
      i >= 0 ==> __CPROVER_forall
      {
        int j;
        j<0 ==> j < i
      }
    },
    "rewrite");
  // clang-format on

  return 0;
}
