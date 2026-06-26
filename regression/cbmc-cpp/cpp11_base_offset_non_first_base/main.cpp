// Derived-to-base pointer adjustment for a NON-FIRST base whose data is
// declared by a further base of its own.
//
// `D : A, C` places the second base `C` at a non-zero offset (after `A`).
// `C`'s only data lives in C's own base `B` (member `B::b`), so in CBMC's
// flattened layout that member is named "B::b" -- it carries no "C::" prefix.
// The only "C::"-prefixed component is C's destructor `C::~C`.  The base
// offset must therefore be derived from the lowest-offset *data* member
// belonging to C's inheritance subtree ({C, B}); a method/code component such
// as the destructor has no per-object storage and must be ignored (its
// member offset is meaningless and previously produced a bogus past-the-end
// offset, so `static_cast<C&>(d)` pointed outside `d`).  N5008 [intro.object]/
// [class.derived]: a non-virtual base subobject occupies a contiguous region,
// so its first data member marks its start.
//
// Non-vacuous: assertion 3 (a wrong value) must FAIL.  The operand `v` is
// nondet so the passing assertions are not constant-folded.

extern "C" void __CPROVER_assert(int, const char *);
extern int nondet_int(void);

struct A
{
  int a;
};
struct B
{
  int b;
};
struct C : B
{
  ~C() {}
};
struct D : A, C
{
};

int main()
{
  D d;
  int v = nondet_int();
  static_cast<A &>(d).a = 111;
  static_cast<C &>(d).b = v; // write through the non-first base C
  __CPROVER_assert(d.b == v, "value written via non-first base C reads back");
  __CPROVER_assert(static_cast<A &>(d).a == 111, "first base A unaffected");
  __CPROVER_assert(d.b == v + 1, "WRONG (must FAIL)");
  return 0;
}
