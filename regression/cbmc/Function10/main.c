void other_func1(int z, int my_func(int b, int c))
{
  my_func(1, 2);
}

void other_func2(int z, int my_func(int b, int c), int y)
{
}

void my_f1(int array[*]);

void my_f1(int array[])
{
}

int main()
{
  int *p;
  my_f1(p);
  
  other_func1(1, 0);
}
