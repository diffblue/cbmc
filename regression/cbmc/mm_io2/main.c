// Memory-mapped I/O read under the wide pointer encoding. The device
// register address is a constant integer cast to a pointer. The wide
// encoding gives such a pointer a dedicated integer-address object, and
// is_integer_address() recognises it (pointer_object is not NULL's, so the
// same_object-based integer_address() the standard encoding relies on would
// not), so the mm_io instrumentation routes the read to __CPROVER_mm_io_r.
char __CPROVER_mm_io_r(void *a, unsigned s)
{
  if((long)a == 0x10)
    return 42;
  return 0;
}

int main()
{
  char *p = (char *)0x10;
  char z = *p;
  __CPROVER_assert(z == 42, "device read routed to MMIO handler");
}
