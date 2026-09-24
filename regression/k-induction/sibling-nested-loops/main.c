// Iterator-invalidation guard: two sibling outer loops, each containing a
// nested inner loop. Processing the first outer loop mutates the goto program;
// if that erased list nodes it would invalidate the natural-loops iterators
// used to process the second outer loop, causing a segfault.
int main()
{
  unsigned i = 0, j;
  while(i < 2)
  {
    j = 0;
    while(j < 2)
      j++;
    __CPROVER_assert(j == 2, "inner loop A terminates at 2");
    i++;
  }

  unsigned m = 0, n;
  while(m < 2)
  {
    n = 0;
    while(n < 2)
      n++;
    __CPROVER_assert(n == 2, "inner loop B terminates at 2");
    m++;
  }
}
