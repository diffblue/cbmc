extern "C" void __CPROVER_assert(bool, const char *);
class A
{
  int i;
  friend class F;

public:
  A() : i(3)
  {
  }
  // N5008 [class.access.nest]/1: a nested class is a member and has the
  // same access rights as any other member
  class B
  {
  public:
    int get(const A &a)
    {
      return a.i;
    }
  };
};
class F
{
public:
  // [class.friend]/2 with [class.access.nest]/1: a class nested in a friend
  // may name the granting class's private members
  class G
  {
  public:
    int get(const A &a)
    {
      return a.i + 1;
    }
  };
};
int main()
{
  A a;
  A::B b;
  F::G g;
  __CPROVER_assert(b.get(a) == 3, "nested class reads a private member");
  __CPROVER_assert(g.get(a) == 4, "class nested in a friend reads it");
  __CPROVER_assert(b.get(a) == 4, "WRONG (must FAIL)");
}
