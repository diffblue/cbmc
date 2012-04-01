struct x
{
  void f();
  void f(int);
  
};

void x::f()
{
}

void x::f(int)
{
}



int main()
{
  &x::f!=0 ; // conversion error
}
