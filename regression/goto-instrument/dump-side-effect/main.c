struct S
{
  int bf : 2;
};

int foo()
{
  return 0;
}

int main()
{
  struct S s;
  struct S *sp = &s;
  if(sp[0].bf = foo())
    return 0;
}
