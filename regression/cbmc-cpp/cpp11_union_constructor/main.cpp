// [class.union]/2 (C++11): a union may have user-defined member functions,
// including constructors.  Such a union is not a POD/trivial type and must be
// constructed via its constructor.  Its implicit copy constructor and copy
// assignment copy the object representation ([class.copy.ctor]/14,
// [class.copy.assign]).  This is the storage shape libstdc++ uses for
// std::optional / std::variant: a union with a constructor that initializes one
// member, wrapped in a struct with an "engaged"/index discriminator.

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
  // direct construction via the union's constructor
  U u(5);
  __CPROVER_assert(u.value == 5, "direct construction via union constructor");

  // copy construction copies the object representation
  U c(u);
  __CPROVER_assert(c.value == 5, "union copy construction");

  // copy assignment copies the object representation
  U d(0);
  d = u;
  __CPROVER_assert(d.value == 5, "union copy assignment");

  // construction through a wrapper struct
  Opt o(7);
  __CPROVER_assert(o.engaged, "wrapper engaged");
  __CPROVER_assert(
    o.payload.value == 7, "union member constructed via union constructor");
  return 0;
}
