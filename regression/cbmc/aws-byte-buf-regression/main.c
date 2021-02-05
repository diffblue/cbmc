int main()
{
  unsigned size;
  __CPROVER_assume(size >= sizeof(short));
  char *buf = __CPROVER_allocate(size, 0);

  short x;
  __CPROVER_assume(sizeof(short) >= 2);

  buf[0] = ((char *)&x)[0];
  buf[1] = ((char *)&x)[1];
}
