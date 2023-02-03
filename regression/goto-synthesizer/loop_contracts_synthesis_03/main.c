#define SIZE 80

void main()
{
  unsigned long len;
  __CPROVER_assume(len <= SIZE);
  __CPROVER_assume(len >= 8);
  char *array = malloc(len);
  const char *end = array + len;
  unsigned s = 0;

  while(array != end)
  {
    s += *array++;
  }
}
