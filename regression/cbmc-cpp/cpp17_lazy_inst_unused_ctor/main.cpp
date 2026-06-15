// Discriminator for N5008 [temp.inst]/11: an unused, non-virtual *constructor*
// of a class template shall not be implicitly instantiated.  Constructors are
// not the virtual carve-out.  The two-argument constructor below is never
// odr-used (the object is default-constructed); under lazy on-odr-use
// instantiation its body -- and the assertion in it -- must not enter the goto
// program, so the forbidden message must be absent.  The default constructor
// IS odr-used and must still be instantiated (s.v is read).
//
// While constructors were instantiated eagerly this was KNOWNBUG (the message
// appeared, vacuously SUCCESS); it becomes CORE once non-virtual constructors
// are deferred too.

template <class T>
struct S
{
  T v;
  S() : v(0) {}
  S(T a, T b)
  {
    __CPROVER_assert(0, "must never appear");
    v = a + b;
  }
};

int main()
{
  S<int> s;
  __CPROVER_assert(s.v == 0, "default-constructed v is 0");
  return 0;
}
