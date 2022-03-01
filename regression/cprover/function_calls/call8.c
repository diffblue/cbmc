void my_function(int *p)
{
  *p;
}

int main()
{
  my_function(0); // not safe
  return 0;
}
