// A reference data member used inside a braced-init-list function argument
// must be dereferenced exactly once.
//
// N5008 [dcl.ref]/1 and [expr.unary.op]/1: a reference denotes the object it
// is bound to; the built-in unary `*` applied to a reference operand yields
// that object.  Passing a braced-init-list argument such as `g({ref, base})`
// constructs a temporary of the parameter's class type; the front-end
// re-type-checked the argument sub-tree while doing so, and re-type-checking
// the reference-member access `this->ref` re-applied its own implicit
// dereference -- corrupting the well-formed `*this->ref` into the ill-formed
// `*(*this->ref)` and rejecting the program with
//   operand of unary * '*this->ref' is not a pointer
// (surfacing in the STL as spurious `instantiating std::__enable_if_t with
// <FALSE, ...>` cascades, e.g. when compiling irep_serialization.cpp's
// `ireps_container.ireps_on_write.insert({h, ireps_container...size()})`).

struct value_pair
{
  unsigned long key;
  unsigned long index;
};

unsigned long combine(const value_pair &p)
{
  return p.key + p.index;
}

// by-value parameter exercises the same braced-init temporary construction
unsigned long combine_by_value(value_pair p)
{
  return p.key * 2 + p.index;
}

struct container
{
  unsigned long &ref; // reference data member -- essential to the defect
  unsigned long base;

  unsigned long via_const_ref()
  {
    // braced-init-list argument that reads the reference data member
    return combine({ref, base});
  }

  unsigned long via_value()
  {
    return combine_by_value({ref, base});
  }
};

int main()
{
  unsigned long v = 40;
  container c{v, 2};

  unsigned long r1 = c.via_const_ref(); // 40 + 2 == 42
  __CPROVER_assert(r1 == 42, "braced-init arg reads reference member once");

  unsigned long r2 = c.via_value(); // 40*2 + 2 == 82
  __CPROVER_assert(r2 == 82, "by-value braced-init arg reads reference member");

  // mutating the referand is observed through the reference member
  v = 100;
  unsigned long r3 = c.via_const_ref(); // 100 + 2 == 102
  __CPROVER_assert(r3 == 102, "reference member observes referand mutation");

  __CPROVER_assert(r1 == 43, "WRONG: must fail");

  return 0;
}
