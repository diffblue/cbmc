extern "C" void __CPROVER_assert(bool, const char *);

// N5008 [expr.static.cast]/2: an lvalue of type "cv1 B" may be cast to
// "reference to cv2 D" when B is a base of D.  The operand here is the
// LVALUE result of `operator*` (a call returning base&); CBMC used to
// reject it ("type mismatch on static_cast") -- fixed 2026-07-21 although the same cast of a
// plain lvalue works -- the call-result shape loses the lvalue-ness
// the reference-downcast path checks for.  The shape of goto_rw.h's
// `static_cast<const range_domaint &>(*ranges)` over a unique_ptr,
// which blocks dog-fooding src/analyses/goto_rw.cpp.
// g++/clang++ accept and verify at runtime.

struct base
{
  virtual ~base()
  {
  }
};

struct derived : base
{
  int x;
};

struct ptrt
{
  base *raw;
  base &operator*() const
  {
    return *raw;
  }
};

int read_x(const ptrt &p)
{
  return static_cast<const derived &>(*p).x;
}

int main()
{
  derived d;
  d.x = 5;
  ptrt p{&d};
  __CPROVER_assert(read_x(p) == 5, "reference downcast of operator* result");
  return 0;
}
