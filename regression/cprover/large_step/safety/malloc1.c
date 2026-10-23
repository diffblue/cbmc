void *malloc(__CPROVER_size_t);

int main()
{
  int *p = malloc(sizeof(int));

  __CPROVER_assert(__CPROVER_LIVE_OBJECT(p), "property 1"); // safe
  __CPROVER_assert(
    __CPROVER_OBJECT_SIZE(p) == sizeof(int), "property 2");         // safe
  __CPROVER_assert(__CPROVER_POINTER_OFFSET(p) == 0, "property 3"); // safe
  __CPROVER_assert(__CPROVER_r_ok(p), "property 4");                // safe
  __CPROVER_assert(__CPROVER_r_ok(p + 1), "property 5");            // unsafe

  return 0;
}
