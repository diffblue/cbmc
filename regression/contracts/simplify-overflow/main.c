int main()
{
  char buf[10];
  __CPROVER_size_t max = 9;
  __CPROVER_size_t start = 1;

  __CPROVER_assert(
    __CPROVER_r_ok(buf + start, max - start), "array is readable");
}
