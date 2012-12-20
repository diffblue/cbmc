// call from outside class

class t
{
public:
  int i;
  static void f() { }
};

int main()
{
  t::f();
}

// call from inside class

class A
{
  static void g();
  static void g(int i);

  void f();
};

void A::f()
{
  g();
}
