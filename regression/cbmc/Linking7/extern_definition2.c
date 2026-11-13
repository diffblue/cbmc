int foo(char *q);

int bar(void)
{
  char c = 1;
  return foo(&c);
}
