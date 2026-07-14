// N5008 [except.ctor]/1-3: during stack unwinding, destructors run for every
// fully constructed automatic object whose scope is exited -- and only those,
// in reverse construction order.  Call-site cases (cross-checked against g++
// and clang++):
//  1. a constructor that throws: the enclosing, fully constructed object is
//     destroyed; the object under construction is NOT ([except.ctor]/2);
//  2. a callee throws past two objects: both destroyed, most recently
//     constructed first.

extern "C" void __CPROVER_assert(int, const char *);

static int destroyed = 0;
static int gdtor = 0;

struct A
{
  ~A()
  {
    ++destroyed;
  }
};

struct B
{
};

struct G
{
  G()
  {
    throw B();
  }
  ~G()
  {
    ++gdtor;
  }
};

static void ctor_throws()
{
  try
  {
    A a;
    G g;
  }
  catch(B &)
  {
    __CPROVER_assert(destroyed == 1, "enclosing object a destroyed");
    __CPROVER_assert(gdtor == 0, "object with throwing constructor NOT destroyed");
  }
}

static int order[2];
static int n = 0;

struct D0
{
  ~D0()
  {
    order[n++] = 0;
  }
};

struct D1
{
  ~D1()
  {
    order[n++] = 1;
  }
};

struct E
{
};

static void f()
{
  throw E();
}

static void reverse_order()
{
  try
  {
    D0 a;
    D1 b;
    f();
  }
  catch(E &)
  {
    __CPROVER_assert(n == 2, "both objects destroyed");
    __CPROVER_assert(
      order[0] == 1 && order[1] == 0, "reverse construction order: b then a");
  }
}

int main()
{
  ctor_throws();
  reverse_order();
  return 0;
}
