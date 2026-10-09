// The __has_trivial_destructor / __is_trivially_destructible builtins must
// compute the actual triviality of a class's destructor per [class.dtor]/8:
// trivial iff the destructor is neither user-provided nor virtual and every
// base and non-static data member is itself trivially destructible.
//
// libstdc++'s std::is_trivially_destructible is defined in terms of
// __has_trivial_destructor, so the previous behaviour -- __has_trivial_destructor
// answering false for every class and __is_trivially_destructible answering
// true for every class -- was doubly unsound and broke the destructor-storage
// selection in optional/variant/pair.  Header-free so it exercises only the
// front-end builtins.

struct Plain
{
  int x;
};
struct UserDtor
{
  ~UserDtor()
  {
  }
};
struct DefDtor
{
  ~DefDtor() = default;
};
struct HasUserDtorMember
{
  UserDtor m;
};
struct Virtual
{
  virtual ~Virtual()
  {
  }
};
struct Derived : UserDtor
{
};
struct Poly
{
  virtual void f();
};

int main()
{
  // __has_trivial_destructor: scalars and classes with a trivial destructor.
  __CPROVER_assert(__has_trivial_destructor(int) == 1, "int has trivial dtor");
  __CPROVER_assert(
    __has_trivial_destructor(Plain) == 1, "Plain has trivial dtor");
  __CPROVER_assert(
    __has_trivial_destructor(UserDtor) == 0, "UserDtor: user-provided dtor");
  __CPROVER_assert(
    __has_trivial_destructor(DefDtor) == 1, "DefDtor: =default is trivial");

  // __is_trivially_destructible: the same triviality, recursively.
  __CPROVER_assert(
    __is_trivially_destructible(Plain) == 1, "Plain trivially destructible");
  __CPROVER_assert(
    __is_trivially_destructible(UserDtor) == 0, "UserDtor not trivial");
  __CPROVER_assert(
    __is_trivially_destructible(HasUserDtorMember) == 0,
    "member with user dtor -> not trivial");
  __CPROVER_assert(
    __is_trivially_destructible(Virtual) == 0, "virtual dtor -> not trivial");
  __CPROVER_assert(
    __is_trivially_destructible(Derived) == 0,
    "base with user dtor -> not trivial");
  // A polymorphic class with a (non-virtual, implicit) trivial destructor is
  // still trivially destructible -- the vtable pointer does not affect it.
  __CPROVER_assert(
    __is_trivially_destructible(Poly) == 1, "Poly: trivial implicit dtor");
  return 0;
}
