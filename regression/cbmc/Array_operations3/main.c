int main()
{
  void *p;
  __CPROVER_array_set(p, 0);
  __CPROVER_assert(
    *(char *)p == 0, "should fail: array_set had no effect on invalid object");
}
