class b
{
public:
  int x;
  
  void f();
};

void b::f()
{
  x=1;
}

class t:public b
{
public:
};

int main()
{
  t instance;
  instance.f();
  assert(instance.x==1);
}
