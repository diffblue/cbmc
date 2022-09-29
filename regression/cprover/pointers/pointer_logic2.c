int main()
{
  int x;
  char *p;
  __CPROVER_size_t offset;

  p = ((char *)&x) + offset;

  __CPROVER_assert(
    __CPROVER_POINTER_OBJECT(p) == __CPROVER_POINTER_OBJECT(&x),
    "property 1"); // should pass
  __CPROVER_assert(
    __CPROVER_POINTER_OFFSET(p) == offset, "property 2"); // should pass

  return 0;
}
