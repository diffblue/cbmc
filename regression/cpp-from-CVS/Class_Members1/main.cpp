class t
{
public:
  int i;
  void f();
  
  void g(double xxx=3.2);
};

void t::f()
{
  i=1;
}

void t::g(double d)
{
  i=(int)d;
}

int main()
{
  t instance;
  instance.f();
  assert(instance.i==1);
  
  instance.g(2.1);
  assert(instance.i==2);
}
