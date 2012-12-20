struct x
{
  void f();
  int f(int);
  
};

void x::f()
{
}

int x::f(int i)
{
  return i;
}



int main()
{
  int (x::*pf) (int) = &x::f;
//  x x1;
//  assert((x1.*pf)(0) == 0);
}
