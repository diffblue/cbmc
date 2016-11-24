void f()
{
  // gcc eats this
  extern int i;
  int j;

  j=11;
  
  assert(i==1);
  
  i=10;
}

int main()
{
  extern int i;
  
  i=1;
  
  f();
  
  assert(i==10);
}

int i;
