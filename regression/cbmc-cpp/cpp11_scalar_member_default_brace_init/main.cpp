// N5008 [dcl.init.list]/3.9: list-initializing a scalar from a braced-init-list
// with a single element initializes the scalar from that element -- so a scalar
// non-static data member with a braced default member initializer, e.g.
// `int x{42}`, is initialized to 42.
//
// CBMC previously left the braced-init-list unconverted for a scalar member's
// default member initializer: the raw `initializer_list` flowed into GOTO
// conversion and aborted the bit-vector flattener.  The equivalent
// `int x = 42;` worked.  g++ and clang++ accept `int x{42};`.
//
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
