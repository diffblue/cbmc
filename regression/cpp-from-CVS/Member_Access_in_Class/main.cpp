class t
{
public:
  void f() { i=1; }

  void g() { f(); }

  int i;
};

int main()
{
  t instance;
  instance.g();
  assert(instance.i==1);
}
