// CORE guard for N5008 [temp.inst]/11 second sentence: a virtual member
// function of a class template MAY be instantiated even if not otherwise
// required, and must work when called through dynamic dispatch.  This is the
// one carve-out where eager instantiation is permitted; Option B must keep
// instantiating reachable virtual members so dispatch is modelled soundly.

template <class T>
struct Base
{
  virtual T id(T x) { return x; }
  virtual ~Base() {}
};

int main()
{
  Base<int> b;
  Base<int> *p = &b;
  __CPROVER_assert(p->id(42) == 42, "virtual dispatch returns argument");
  return 0;
}
