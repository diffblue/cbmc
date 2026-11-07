// C++20 compound-requirement with a return-type-requirement:
//   { E } -> C   is satisfied iff E is valid and C<decltype((E))> holds.
// Per [expr.prim.req.compound]/1 and [dcl.type.decltype]/1, decltype((++a)) is
// an lvalue-reference (pre-increment of an arithmetic lvalue is an lvalue,
// [expr.pre.incr]/1), so SameAs<decltype((++a)), int&> holds for T=int.

template <class A, class B>
concept SameAs = __is_same(A, B);

template <class T>
concept PreIncReturnsRef = requires(T a) {
  { ++a } -> SameAs<T &>;
};

template <class T>
concept PlusReturnsValue = requires(T a) {
  { a + a } -> SameAs<T>;
};

int main()
{
  static_assert(PreIncReturnsRef<int>, "++int is int&");
  static_assert(PlusReturnsValue<int>, "int+int is int");
  return 0;
}
