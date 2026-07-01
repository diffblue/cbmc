// N5008 [dcl.init.list]/3.9: list-initializing a scalar from a braced-init-list
// with a single element initializes the scalar from that element -- so a scalar
// non-static data member with a braced default member initializer, e.g.
// `int x{42}`, is initialized to 42.
//
// CBMC leaves the braced-init-list unconverted for a scalar member's default
// member initializer: the raw `initializer_list` flows into GOTO conversion and
// aborts the bit-vector flattener ("Reached unimplemented
// boolbv_widtht::get_entry()").  The equivalent `int x = 42;` works.  g++ and
// clang++ accept `int x{42};`.
//
// KNOWN BUG: a braced (as opposed to `=`) default member initializer of a
// scalar member is not reduced to its single element.  Flip to CORE once the
// single-element braced-init-list is unwrapped for scalar members.
// assertion.2 must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

struct Holder
{
  int x{42}; // braced default member initializer of a scalar member
};

int main()
{
  Holder h;
  __CPROVER_assert(h.x == 42, "braced default member initializer of scalar");
  __CPROVER_assert(h.x != 42, "WRONG must FAIL");
  return 0;
}
