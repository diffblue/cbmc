// Phase 3.1: Constraint subsumption for function overload resolution
// Two function templates with different constraints on the same
// parameter. Without subsumption checking, this is ambiguous.

template<class T>
concept Integral = __is_integral(T);

template<class T>
concept SignedIntegral = Integral<T> && __is_signed(T);

// Overload 1: any integral
template<class T> requires Integral<T>
int classify(T) { return 1; }

// Overload 2: signed integral (more constrained, subsumes Overload 1)
template<class T> requires SignedIntegral<T>
int classify(T) { return 2; }

int main()
{
  // int is both Integral and SignedIntegral.
  // With proper subsumption, overload 2 should be selected.
  // Without it, CBMC may report ambiguity or pick the wrong one.
  __CPROVER_assert(classify(42) == 2, "SignedIntegral subsumes Integral");
}
