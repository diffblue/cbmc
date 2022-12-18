#define SIZE 80

void main()
{
  unsigned long len;
  __CPROVER_assume(len <= SIZE);
  __CPROVER_assume(len >= 8);
  char *array = malloc(len);
  unsigned long s = 0;

  unsigned long j = 0;
  for(unsigned long i = 0; i < len; i++)
  {
    s += array[j];
    j++;
  }
}
