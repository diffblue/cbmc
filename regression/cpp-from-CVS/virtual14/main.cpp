struct T
{
  int x, y;
};

class A
{
  public:
  int a;
  virtual void f( T t1, T& t2)
  {
    t2.x = t1.x;
    t2.y = t1.y;
  }
};


class B
{
  public:
  int b;

 virtual void f(T t1, T& t2)
  {
    t2.x = t1.y;
    t2.y = t1.x;
  }
};

class C: public A , public B
{
public:
  virtual void f(T t1, T& t2)
  {
    t2.x = t1.x+1;
    t2.y = t1.y+1;
  }
};

int main(int argc, char* argv[])
{
  A a;
  B b;
  C c;
  T t1, t2;

  t1.x = 10;
  t1.y = 20;

  a.f(t1,t2);
  assert(t2.x == t1.x && t2.y == t1.y);
  t2.x = t2.y = 0;

  b.f(t1,t2);
  assert(t2.x == t1.y && t2.y == t1.x);
  t2.x = t2.y = 0;

  c.f(t1,t2);
  assert(t2.x == t1.x+1 && t2.y == t1.y+1);
  t2.x = t2.y = 0;

  ((A*)&c)->f(t1,t2);
  assert(t2.x == t1.x+1 && t2.y == t1.y+1);
  t2.x = t2.y = 0;


  c.b = 1;
  assert(((B*)&c)->b == 1);

  ((B*)&c)->f(t1,t2);
  assert(t2.x == t1.x+1 && t2.y == t1.y+1);
  t2.x = t2.y = 0;

  return 0;
}
