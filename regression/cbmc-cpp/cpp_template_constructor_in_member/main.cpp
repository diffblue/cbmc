// A non-template class that has a constructor template, constructed with the
// braced form `M{...}` from inside one of its own member functions.  Inside the
// class the injected-class-name 'M' makes the constructor template visible
// under the bare name, but `M{...}` is an ordinary construction, not a
// class-template-argument-deduction context ([dcl.type.class.deduct] applies
// only to a class template).  This mirrors libstdc++'s __max_size_type, whose
// operator~ returns `_Max_size_type{~_M_val, ...}` from inside the class.

extern "C" unsigned long __VERIFIER_nondet_ulong();
extern "C" void __CPROVER_assert(int, const char *);

struct M
{
  unsigned long v;
  bool msb;
  M() = default;
  // Converting constructor template.
  template <typename T>
  M(T i) : v(i), msb(false)
  {
  }
  // Two-argument constructor used by the in-member braced construction.
  M(unsigned long x, bool m) : v(x), msb(m)
  {
  }
  // Braced construction of M from inside a member function.
  M neg() const
  {
    return M{~v, !msb};
  }
};

int main()
{
  unsigned long x = __VERIFIER_nondet_ulong();
  M a{x};
  M r = a.neg();
  __CPROVER_assert(r.v == ~x, "in-member braced construction computes ~v");
  __CPROVER_assert(r.msb == true, "in-member braced construction sets msb");
  return 0;
}
