// Regression for [over.match.oper]/9 + [over.built]: when a binary
// operator with no viable non-member or member operator overload is
// processed, the operator is treated as a built-in operator per
// [over.built]; the operands must then be subject to standard or
// user-defined conversion sequences to the built-in operator's
// parameter types.
//
// Concretely, for `T > 0` where `T` is a class with
// `operator long() const` (e.g., `std::fpos<mbstate_t>` whose
// `operator streamoff()` materialises the user-defined conversion
// to `long`), the conversion sequence
//
//   T -> long           (user-defined)
//   long > int          (built-in)
//
// must apply.  CBMC's C parent-class implementation of
// `implicit_typecast_arithmetic(exprt&, exprt&)` only knows about C's
// arithmetic standard conversions; the struct operand reaches
// `c_typecastt::implicit_typecast_arithmetic` unchanged and surfaces
// as the spurious diagnostic
//
//   conversion from 'struct fpos' to 'signed int':
//   implicit arithmetic conversion not permitted
//
// even though the user-defined conversion to `long` is unambiguous.
//
// Visible symptom on CBMC's own source: `if(this->tellp() > 0)` at
// `src/util/message.h:250`.  `tellp()` returns
// `std::fpos<mbstate_t>` whose `operator streamoff()` is the
// user-defined conversion to `long`.  Every translation unit that
// includes `<message.h>` (10+ files in the dog-food set) hit this.
//
// The fix overrides
// `cpp_typecheckt::implicit_typecast_arithmetic(exprt&, exprt&)` (and
// the unary form): when an operand's type is a class with a single
// arithmetic-typed user-defined conversion operator, apply the
// conversion via `implicit_typecast` first so the C parent's
// arithmetic typecheck sees two arithmetic operands.

template <typename T>
class fpos
{
private:
  long _M_off;

public:
  fpos() : _M_off(0)
  {
  }
  // User-defined conversion to long (mirrors libstdc++
  // `fpos<mbstate_t>::operator streamoff()`).
  operator long() const
  {
    return _M_off;
  }
};

fpos<int> get_fpos()
{
  return fpos<int>();
}

int main()
{
  // Rvalue path (function-return temporary).  Pre-fix: hits the
  // "implicit arithmetic conversion not permitted" diagnostic.
  if(get_fpos() > 0)
    return 1;

  // Lvalue path (named local).  Pre-fix: also hits the diagnostic
  // (verification still claims success because the comparison
  // simplifies to false, but the diagnostic surfaces and the test
  // descriptor's negative pattern catches it).
  fpos<int> p;
  if(p > 0)
    return 2;

  return 0;
}
