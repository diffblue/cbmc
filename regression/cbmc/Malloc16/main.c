void *malloc(__CPROVER_size_t);

int foo(int *x)
{
  *x = 1;
}

int main()
{
  void *tmp;
  int *dev;

  tmp = malloc(sizeof(int));
  dev = (int*)tmp;
  
  void *r = (void*)0;
  unsigned int q = r;
  unsigned int p = dev;
  if(p != q)
  {
    foo(dev);
    __CPROVER_assert(*dev==1, "WTF?");
  }
  return 0;
}
