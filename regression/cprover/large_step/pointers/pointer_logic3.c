int main()
{
  char *base, *p;
  __CPROVER_size_t size, offset;

  __CPROVER_assume(__CPROVER_r_ok(base, size));

  if(offset < size)
  {
    p = base + offset;

    __CPROVER_assert(
      __CPROVER_same_object(base, p), "property 1"); // should pass
    __CPROVER_assert(base <= p, "property 2");       // should pass
    __CPROVER_assert(p < base + size, "property 3"); // should pass
  }

  return 0;
}
