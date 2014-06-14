int global;

void f(int farg)
{
  global=1;
}

void g(int garg)
{
  global=0;
}

int main()
{
  void (*p)(int);
  __CPROVER_bool c;
  
  p=c?f:g;
  
  p(1);
  
  assert(global==c);
}
