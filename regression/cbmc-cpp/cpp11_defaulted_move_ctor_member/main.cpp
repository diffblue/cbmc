// N5008 [class.copy.ctor]/14-15: a defaulted move constructor
// direct-initializes each base and non-static data member from the
// corresponding subobject of the argument, cast to an xvalue
// (`static_cast<M&&>(other.m)`).  Overload resolution on that xvalue selects
// the member's *move* constructor.  For a member whose copy constructor is
// deleted but whose move constructor is usable, the move constructor must be
// chosen; choosing the deleted copy constructor is ill-formed.
//
// CBMC's defaulted copy/move constructor synthesis only generates the
// memberwise initializers when every member is trivially copyable; for a
// non-trivially-copyable member (here M, with a deleted copy constructor and a
// user-provided move constructor) it falls back to a member initializer that
// selects M's *copy* constructor, which is deleted -- reported as
//   member 'M::M(this, ...M&...)' is not accessible
// followed by a CONVERSION ERROR that drops the enclosing constructor body.
// g++ and clang++ accept this program.  This is the header-free root cause of
// the enable_if_t<false> dog-food failures in parse_options.cpp,
// irep_serialization.cpp and ui_message.cpp (all hold std::unique_ptr members,
// whose copy constructor is deleted and move constructor is user-provided).
//
// KNOWN BUG: requires defaulted move/copy constructor synthesis to
// move/copy-construct non-trivially-copyable members via the member's own
// move/copy constructor (with the correct value category).  Flip to CORE once
// that is implemented.
// assertion.2 must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

struct M
{
  int v;
  M() : v(0)
  {
  }
  M(const M &) = delete;
  M(M &&other) : v(other.v)
  {
    other.v = -1;
  }
};

struct Holder
{
  M m;
  Holder()
  {
  }
  Holder(Holder &&) = default;
};

int main()
{
  Holder h;
  h.m.v = 42;
  Holder h2(static_cast<Holder &&>(h));
  __CPROVER_assert(h2.m.v == 42, "move-constructed member holds moved value");
  __CPROVER_assert(h2.m.v != 42, "WRONG must FAIL");
  return 0;
}
