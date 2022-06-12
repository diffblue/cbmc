int x;

int main()
{
  __CPROVER_assert(__CPROVER_pointer_in_range(&x, &x, &x), "property 1");
  __CPROVER_assert(__CPROVER_pointer_in_range(&x, &x, &x + 1), "property 2");
  __CPROVER_assert(
    __CPROVER_pointer_in_range(&x, &x + 1, &x + 1), "property 3");
  __CPROVER_assert(!__CPROVER_pointer_in_range(&x, &x + 1, &x), "property 4");
  __CPROVER_assert(!__CPROVER_pointer_in_range(0, &x, &x), "property 5");
  __CPROVER_assert(!__CPROVER_pointer_in_range(&x, 0, &x), "property 6");
  __CPROVER_assert(!__CPROVER_pointer_in_range(&x, &x, 0), "property 7");
}
