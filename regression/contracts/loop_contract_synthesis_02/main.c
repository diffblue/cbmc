#define SIZE 80

void main()
{
  unsigned len;
  __CPROVER_assume(len <= SIZE);
  __CPROVER_assume(len >= 8);
  char *array = malloc(len);
  unsigned s = 0;

  for(unsigned i = 0; i < SIZE; ++i)
  {
    if(i == len - 1)
      break;
    s += array[i];
  }
}
