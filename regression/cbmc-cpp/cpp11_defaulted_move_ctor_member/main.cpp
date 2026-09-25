// N5008 [class.copy.ctor]/14-15: a defaulted move constructor
// direct-initializes each base and non-static data member from the
// corresponding subobject of the argument, cast to an xvalue
// (`static_cast<M&&>(other.m)`).  Overload resolution on that xvalue selects
// the member's *move* constructor.  For a member whose copy constructor is
// deleted but whose move constructor is usable, the move constructor must be
// chosen; choosing the deleted copy constructor is ill-formed.
//
// CBMC's defaulted copy/move constructor synthesis previously generated a
// memberwise *copy* initializer `m(ref.m)` for the move constructor too, so a
// non-trivially-copyable member (here M, with a deleted copy constructor and a
// user-provided move constructor) selected M's deleted copy constructor --
// reported as "member 'M::M(this, ...M&...)' is not accessible" followed by a
// CONVERSION ERROR that dropped the enclosing constructor body.  The fix emits
// a move initializer (static_cast<T&&>(ref.member)) for the move constructor,
// so the member's move constructor is selected ([class.copy.ctor]/15).  This
// was the header-free, template-free root cause of the enable_if_t<false>
// dog-food failures in irep_serialization.cpp and ui_message.cpp (which hold a
// std::unique_ptr member, whose copy constructor is deleted and move
// constructor is user-provided).
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
