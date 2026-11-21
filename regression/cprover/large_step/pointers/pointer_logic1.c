int main()
{
  char *p;
  __CPROVER_size_t offset;

  p = (char *)0 + offset;

  __CPROVER_assert(
    __CPROVER_POINTER_OBJECT(p) == 0, "property 1"); // should pass
  __CPROVER_assert(
    __CPROVER_POINTER_OFFSET(p) == offset, "property 2"); // should pass

  return 0;
}
