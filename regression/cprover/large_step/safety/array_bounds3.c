int main()
{
  const __CPROVER_size_t array_len;
  const unsigned char *array_bytes;

  __CPROVER_assume(__CPROVER_LIVE_OBJECT(array_bytes));
  __CPROVER_assume(array_len >= 1);
  __CPROVER_assume(__CPROVER_OBJECT_SIZE(array_bytes) == array_len);
  __CPROVER_assume(__CPROVER_POINTER_OFFSET(array_bytes) == 0);

  array_bytes[0];
}
