// [class.union]/2 (C++11): a union may have user-defined member functions,
// including constructors.  This is the storage shape libstdc++ uses for
// std::optional / std::variant: a union with a constructor that initializes one
// member, wrapped in a struct with an "engaged"/index discriminator.  CBMC does
// not yet construct a union via its user-defined constructor (it attempts an
// implicit conversion instead), which is why `std::optional<int> o = 5;`
// followed by `o.value()` currently fails.

union U
{
  char empty;
  int value;
  U(int x) : value(x) {} // a union constructor initialising one member
};

struct Opt
{
  U payload;
  bool engaged;
  Opt(int x) : payload(x), engaged(true) {}
};

int main()
{
  U u(5);
  __CPROVER_assert(u.value == 5, "direct construction via union constructor");

  Opt o(7);
  __CPROVER_assert(o.engaged, "wrapper engaged");
  __CPROVER_assert(
    o.payload.value == 7, "union member constructed via union constructor");
  return 0;
}
