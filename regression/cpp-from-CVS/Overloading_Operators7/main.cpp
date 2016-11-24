int g;

struct A
{
  int i;
  A(int i):i(i){}

  friend bool operator==(const A& a1, const A& a2)
  {
    g=10;
    return a1.i==a2.i;
  }
};

int main()
{
  A a1(1);
  A a2(2);
  assert(!(a1 == a2));
  assert(g==10);
}
