// An explicitly-defaulted (`= default`) copy or move constructor has the
// same effect as the implicitly-defined one: it memberwise copies/moves the
// base subobjects and non-static data members ([dcl.fct.def.default],
// [class.copy.ctor]/14).  Previously CBMC synthesised an empty body for a
// user-written `= default` copy/move constructor (only the implicit,
// undeclared one received the memberwise copy), leaving the members of the
// constructed object indeterminate.  This is the shape relied upon by
// std::pair (`pair(pair&&) = default`), which std::set/std::map use to return
// the insert position.
//
// The memberwise copy is generated at conversion time (when the class is
// fully formed), for trivially-copyable bases/members.

template <class A, class B>
struct Pair
{
  A first;
  B second;
  Pair() = default;
  Pair(const Pair &) = default;
  Pair(Pair &&) = default;
};

struct Base
{
  int b = 0;
};

template <class T>
struct Derived : Base
{
  T m;
  Derived() = default;
  Derived(const Derived &) = default;
  Derived(Derived &&) = default;
};

struct NonTemplate
{
  int x;
  int *y;
  NonTemplate() = default;
  NonTemplate(NonTemplate &&) = default;
};

int main()
{
  Pair<int, int> p;
  p.first = 11;
  p.second = 22;

  const Pair<int, int> &pr = p;
  Pair<int, int> copied(pr);
  __CPROVER_assert(copied.first == 11, "defaulted copy ctor copies first");
  __CPROVER_assert(copied.second == 22, "defaulted copy ctor copies second");

  Pair<int, int> moved(static_cast<Pair<int, int> &&>(p));
  __CPROVER_assert(moved.first == 11, "defaulted move ctor moves first");
  __CPROVER_assert(moved.second == 22, "defaulted move ctor moves second");

  Derived<int> d;
  d.b = 5;
  d.m = 7;
  Derived<int> dcopy(d);
  __CPROVER_assert(dcopy.b == 5, "defaulted copy ctor copies base subobject");
  __CPROVER_assert(dcopy.m == 7, "defaulted copy ctor copies derived member");

  int local = 9;
  NonTemplate nt;
  nt.x = 3;
  nt.y = &local;
  NonTemplate ntmoved(static_cast<NonTemplate &&>(nt));
  __CPROVER_assert(ntmoved.x == 3, "non-template defaulted move copies x");
  __CPROVER_assert(ntmoved.y == &local, "non-template defaulted move copies y");

  return 0;
}
