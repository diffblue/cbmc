// Regression for [class.copy.ctor]/1 + [dcl.init]/14: copy-initialization
// from `const T&` to a converting-constructor parameter of type `T`.
//
// CBMC's `user_defined_conversion_sequence` handles the
// "convert source struct to constructor's first parameter struct" case
// by reducing it to a derived-to-base pointer conversion:
//
//     struct From*  ->  struct ParamT*
//
// via `standard_conversion_sequence`.  When `From == ParamT` modulo
// cv-qualifiers — i.e., the canonical copy-initialization case — the
// pointer conversion is from `const struct T*` to `struct T*`, which
// `standard_conversion_sequence` correctly REJECTS as a discarding-of-const
// not allowed by [conv.qual].
//
// The conversion sequence the compiler should pick per [class.copy.ctor]/1
// is the copy constructor `T(const T&)` invoked on the converting-ctor's
// `T` parameter — but CBMC's loop never tried that because it tested
// the pointer-conversion path with the qualified pointer.
//
// Symptom in CBMC's own source: `simplify_expr_array.cpp`,
// `simplify_expr_boolean.cpp`, `simplify_expr_floatbv.cpp`,
// `simplify_expr_struct.cpp`, `substitute_symbols.cpp` — all of which
// have helpers that return `const exprt&` (or `const exprt`) and rely on
// converting to a `resultt<exprt>` return-type via its `resultt(exprt)`
// converting constructor.  Without this fix:
//
//     invalid implicit conversion from 'const struct exprt' to 'struct resultt'
//
// breaks every translation unit using the pattern.
//
// The fix strips cv-qualifiers from the source's type before computing
// the address-of for the pointer-conversion check.  The conversion is
// still a user-defined conversion (constructor call) so the rank
// adjustment is unchanged.

struct exprt
{
  int x;
  exprt() : x(0)
  {
  }
  exprt(const exprt &) = default;
};

template <typename T = exprt>
struct resultt
{
  T expr;
  // Converting constructor: takes the parameter by value.
  // NOLINTNEXTLINE(runtime/explicit)
  resultt(T _expr) : expr(static_cast<T &&>(_expr))
  {
  }
};

const exprt &get_const_expr_ref()
{
  static exprt e;
  return e;
}

exprt get_const_expr_value()
{
  return exprt{};
}

// Function returning `resultt<exprt>` whose body returns `const exprt&`.
resultt<> from_const_ref()
{
  return get_const_expr_ref();
}

// Variant: return a `const exprt` (by-value) into the same return type.
resultt<> from_const_value()
{
  return get_const_expr_value();
}

int main()
{
  resultt<> a = from_const_ref();
  resultt<> b = from_const_value();
  (void)a;
  (void)b;
  return 0;
}
