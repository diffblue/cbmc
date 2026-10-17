int main()
{
  const __CPROVER_size_t array_len;
  const unsigned char *array_bytes;

  __CPROVER_assume(array_len >= 1);
  __CPROVER_assume(__CPROVER_r_ok(array_bytes, array_len));
  __CPROVER_assert(__CPROVER_r_ok(array_bytes, 1), "property 1");
}
