int main()
{
  __CPROVER_assert(
    __CPROVER_forall {
      int i;
      ({
        goto out;
        i == i;
      })
    },
    "");
  __CPROVER_assert(
    __CPROVER_forall {
      int i;
      ({ i == i; })
    },
    "");
out:

  return 0;
}
