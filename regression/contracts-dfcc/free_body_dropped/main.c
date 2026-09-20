void free(void *ptr)
{
}

void foo(void *p)
{
  free(p);
}

int main()
{
  int x = 42;
  return 0;
}
