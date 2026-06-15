// Discriminator for N5008 [temp.inst]/11: an unused, non-virtual *destructor*
// of a class template shall not be implicitly instantiated.  No object of
// S<int> is ever created, so ~S() is never odr-used; only the static member
// sval() is used.  Under lazy on-odr-use instantiation ~S()'s body -- and the
// assertion in it -- must not enter the goto program, so the forbidden message
// must be absent.
//
// While destructors were instantiated eagerly this was KNOWNBUG (the message
// appeared, vacuously SUCCESS); it becomes CORE once non-virtual destructors
// are deferred too.

template <class T>
struct S
{
  T v;
  static int sval() { return 7; }
  ~S() { __CPROVER_assert(0, "must never appear"); }
};

int main()
{
  __CPROVER_assert(S<int>::sval() == 7, "static member used, no object created");
  return 0;
}
