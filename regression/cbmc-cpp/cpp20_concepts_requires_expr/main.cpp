// requires-expression with expression requirements:
// requires(T x) { x + 1; } checks if x + 1 is a valid expression

template<class T, class U>
  requires requires(T a, U b) { a + b; }
auto add(T a, U b) { return a + b; }

// Compound requirement with return type constraint
// requires(T x) { { x.size() } -> same_as<int>; }

int main()
{
  __CPROVER_assert(add(1, 2) == 3, "add ints");
  __CPROVER_assert(add(1.5, 2.5) == 4.0, "add doubles");
}
