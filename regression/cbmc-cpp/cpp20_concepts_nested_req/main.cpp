// Phase 3.3: Nested requirements
// requires { requires expr; } — evaluates expr as a boolean constraint.

template<class T>
concept SmallType = requires {
  requires sizeof(T) <= 4;
};

template<class T>
int check(T) { return 0; }

template<SmallType T>
int check(T) { return 1; }

int main()
{
  // double is 8 bytes, so it should NOT satisfy SmallType.
  // Without nested requirement evaluation, CBMC skips the
  // constraint and returns 1.
  __CPROVER_assert(check(3.14) == 0, "double is not SmallType");
}
