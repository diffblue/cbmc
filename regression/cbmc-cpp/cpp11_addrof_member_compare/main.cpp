// Per [dcl.init.ref]/5 and [expr.eq]/3:
// Pointer-to-member-function types must be preserved consistently
// through address_of, simplification, and comparison with NULL, so
// that binary_relation_exprt (validated by --validate-ssa-equation)
// sees matching types on both operands.
//
// The simplifier reduces patterns like !(ptr != 0) to ptr == 0.
// During symex, dereference_rec rewrites address_of(x::f) via
// address_arithmetic which uses the one-argument address_of_exprt
// constructor.  That constructor builds pointer_type(op.type()) and
// previously did not carry over the outer pointer's to_member
// attribute.  The other side — a NULL constant — retained to_member,
// so binary_relation_exprt::validate reported a type mismatch.
//
// Apple libc++'s assert() macro expands to '!(cond)' so this pattern
// was exposed by Address_of_Method1 on macOS.

struct x
{
  void f();
  static int i;
};

void x::f()
{
}

int main()
{
  // The !(expr) form exercises the simplifier's !(a!=b) -> a==b rule
  // on pointer-to-member-function and pointer-to-member-object.
  if(!(&x::f != 0))
    return 1;
  if(!(&x::i != 0))
    return 2;
  return 0;
}
