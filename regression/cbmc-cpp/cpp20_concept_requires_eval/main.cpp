// C++20 concept evaluation: a concept whose constraint-expression is a
// requires-expression (simple requirement + type requirement) is evaluated as
// a constexpr bool, and a concept-id is usable as a value (here as a non-type
// bool template argument selecting a branch of a conditional).  Grounded in
// N5008 [expr.prim.req.simple]/1, [expr.prim.req.type]/1, [temp.names]/9.

template <bool B, class T, class F>
struct cond
{
  using type = F;
};
template <class T, class F>
struct cond<true, T, F>
{
  using type = T;
};

// simple-requirement: satisfied iff `a + a` is a valid expression.
template <class T>
concept Addable = requires(T a) { a + a; };

// type-requirement: satisfied iff T::value_type names a type.
template <class T>
concept HasValueType = requires { typename T::value_type; };

struct WithVT
{
  using value_type = int;
};

int main()
{
  // Addable<int> is true; Addable<WithVT> is false (no operator+).
  static_assert(Addable<int>, "int is addable");
  static_assert(HasValueType<WithVT>, "WithVT has value_type");

  // concept-id as a non-type bool template argument: picks branch T for true.
  typename cond<Addable<int>, int, char>::type picked_true = 0;
  __CPROVER_assert(sizeof(picked_true) == sizeof(int), "Addable<int> selected int");

  return 0;
}
