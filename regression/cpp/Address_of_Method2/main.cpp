struct x
{
  void f();
};

void x::f()
{
}

int main()
{
  x a;
  void *p;
  
  // this should fail
  p=a.f;
}
