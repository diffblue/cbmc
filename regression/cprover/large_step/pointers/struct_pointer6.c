struct buf
{
  __CPROVER_size_t len;
};

int main()
{
  struct buf *b;
  __CPROVER_assume(__CPROVER_r_ok(b)); // must not alias with x
  __CPROVER_assume(b->len == 456);

  __CPROVER_size_t x, *size_t_ptr = &x;
  *size_t_ptr = 123;

  __CPROVER_assert(b->len == 456, "property 1");
}
