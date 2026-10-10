int main()
{
  const __CPROVER_size_t array_len, i;
  const unsigned char *array_bytes;

  __CPROVER_assume(i < array_len);
  __CPROVER_assume(__CPROVER_POINTER_OFFSET(array_bytes) == 0);
  __CPROVER_assume(__CPROVER_r_ok(array_bytes, array_len));
  __CPROVER_assert(__CPROVER_r_ok(array_bytes + i, 1), "property 1");
}
