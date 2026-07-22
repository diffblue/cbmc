#define SIZE 80

void main()
{
  unsigned long long len;
  __CPROVER_assume(len >= 8 && len <= __CPROVER_max_malloc_size);
  char *array = malloc(len);
  const char *end = array + len;
  unsigned s = 0;

  while(array != end)
  {
    s += *array++;
  }
}
