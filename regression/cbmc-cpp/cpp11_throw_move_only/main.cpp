// N5008 [except.handle]/1-3: a handler `catch(T &e)` (or `catch(T e)`) declares
// the exception variable, whose value is the exception object.  The front-end
// must declare that variable without synthesising a spurious constructor.
//
// CBMC initialized the catch variable with an `int` 0 placeholder ("its value
// comes from the exception at runtime"); for a *class*-typed catch variable
// this made the type-checker construct the class FROM an int -- reported as
//   found no match for symbol 'Ex' ... argument types: signed int
// and dropped with a CONVERSION ERROR.  It failed for every class type without
// a matching int constructor, including move-only classes (whose copy
// constructor is deleted, and which have no int constructor) -- so a
// `catch(MoveOnly &)` clause could not be type-checked at all.  g++ and clang++
// accept this program.  The fix nondet-initializes the catch variable of any
// type instead of constructing it from an int placeholder.
//
// This is the root cause of the enable_if_t<false> / "no match ... signed int"
// failure when compiling CBMC's own parse_options.cpp with goto-cc (it catches
// exceptions transitively holding a move-only, std::unique_ptr-backed
// ui_message_handlert).
//
// Note: CBMC does not currently propagate the thrown value into a catch handler
// (throw/catch of even a copyable class or an int leaves the handler body
// unreachable), so this test verifies the *type-checking* of a move-only catch
// clause via a reachable, non-vacuous assertion before the try; the
// exception-value propagation is a separate limitation.
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
  }
};

struct Ex
{
  M m;
  Ex()
  {
  }
  Ex(Ex &&) = default; // move-only exception type
};

int main()
{
  int reached = 5;
  __CPROVER_assert(reached == 5, "reachable state before try");
  __CPROVER_assert(reached != 5, "WRONG must FAIL");
  // Exercises type-checking of a catch clause for a move-only class type
  // (previously a CONVERSION ERROR).
  try
  {
    throw Ex();
  }
  catch(Ex &)
  {
  }
  return 0;
}
