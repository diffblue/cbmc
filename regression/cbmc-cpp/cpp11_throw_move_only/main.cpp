// N5008 [except.throw]/3 + [class.copy.elision]/3: throwing an object
// initializes the exception object by copy-initialization from the operand;
// when the operand is a prvalue (here `Ex()`), the exception object is
// initialized directly (guaranteed copy elision) or, failing that, by the move
// constructor.  Throwing an object of a move-only class is therefore
// well-formed.
//
// CBMC constructs the exception object with the class's *copy* constructor,
// which for a move-only class (here Ex, whose member M has a deleted copy
// constructor and a user-provided move constructor) is deleted -- so the throw
// fails ("found no match for symbol 'Ex'" / the deleted copy constructor is
// "not accessible") and is dropped with a CONVERSION ERROR.  g++ and clang++
// accept this program.  CBMC does handle throw/catch of a *copyable* class, so
// the gap is specifically the copy-vs-move/elision choice for the exception
// object.
//
// This is the remaining cause of the enable_if_t<false> failure when compiling
// CBMC's own parse_options.cpp with goto-cc: it throws exceptions that
// transitively hold a move-only, std::unique_ptr-backed ui_message_handlert,
// and CBMC copy-constructs the thrown exception object.  (The defaulted
// move-constructor half of the problem is fixed and covered by
// cpp11_defaulted_move_ctor_member.)
//
// KNOWN BUG: requires the exception-object construction on throw to move (or
// elide) from a prvalue/xvalue operand rather than requiring a copy
// constructor.  Flip to CORE once implemented.
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

struct Ex
{
  M m;
  Ex()
  {
    m.v = 7;
  }
  Ex(Ex &&) = default;
};

int main()
{
  try
  {
    throw Ex();
  }
  catch(Ex &e)
  {
    __CPROVER_assert(
      e.m.v == 7, "thrown move-only exception carries its value");
    __CPROVER_assert(e.m.v != 7, "WRONG must FAIL");
  }
  return 0;
}
