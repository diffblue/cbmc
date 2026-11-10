// N5008 [stmt.ranged]: a range-based for over an array.
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int a[] = {1, 2, 3};
  int s = 0;
  for(int x : a)
    s += x;
  __CPROVER_assert(s == 6, "range-based for");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
