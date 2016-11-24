struct x
{
  void f();
  
  static int i;
};

void x::f()
{
}

int main()
{
  assert(&x::f!=0);
  
  assert(&x::i!=0);
}
