int my_function(void)
{
  return 10;
}

typedef int (*fptrt)(void);

int main()
{
  fptrt fptr1 = my_function;
  fptrt fptr2 = 0;

  fptr1(); // safe
  fptr2(); // unsafe

  return 0;
}
