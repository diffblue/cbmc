// Discriminator for N5008 [temp.inst]/11: an unused, non-virtual *operator*
// member of a class template shall not be implicitly instantiated.  Operators
// are not the virtual carve-out, so the same rule as ordinary member functions
// applies.  operator+ below is never odr-used; under lazy on-odr-use
// instantiation its body -- and the assertion in it -- must not enter the goto
// program.  The forbidden message must therefore be absent.
//
// While operators were instantiated eagerly this was KNOWNBUG (the message
// appeared, vacuously SUCCESS); it becomes CORE once non-virtual operators are
// deferred too.

template <class T>
struct S
{
  T v;
  void use() { v = v; }
  S operator+(const S &) const
  {
    __CPROVER_assert(0, "must never appear");
    return *this;
  }
};

int main()
{
  S<int> s;
  s.v = 1;
  s.use();
  __CPROVER_assert(s.v == 1, "v preserved");
  return 0;
}
