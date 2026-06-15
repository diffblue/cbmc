// A class-template partial specialization whose argument pattern is itself a
// nested class-template-id -- `base<holder<T>>` (N5008 [temp.spec.partial]).
// This is the libstdc++ `allocator_traits<allocator<T>>` shape.
//
// Per [temp.spec.partial.match]/2 the specialization matches `base<holder<int>>`
// because `T` can be deduced (T == int), so the instantiation must be generated
// from the partial specialization and expose its member typedef `cp`.
//
// Previously, naming the member through a qualified-id at namespace scope
// (`typedef base<holder<int>>::cp X;`) reached partial-specialization matching
// with the nested template-id argument `holder<int>` still un-elaborated -- a
// type-naming declaration of the same type elaborates `holder<int>` as a side
// effect, but the qualified-name path did not.  The match then failed and fell
// back to the body-less primary template, leaving `base<holder<int>>` an empty
// (truncated) class, so `::cp` was unknown.  Per [temp.inst]/2 the argument's
// completeness affects the semantics here, and [temp.spec.general]/7 requires
// the instantiation to be the same regardless of which context first required
// it.  See doc/architectural/cpp-requires-expression-support.md.

template <typename>
struct holder
{
};

template <typename>
struct base;

template <typename T>
struct base<holder<T>>
{
  using cp = T;
  cp value;
};

// Namespace-scope qualified-name use -- the failing context.
typedef base<holder<int>>::cp X;

int main()
{
  // The member typedef must resolve to `int`.
  X x = 42;
  __CPROVER_assert(x == 42, "member typedef cp resolves to int");

  // The class itself must be the (complete) partial specialization, with its
  // `value` member of type `cp` == int.
  base<holder<int>> b;
  b.value = 7;
  __CPROVER_assert(b.value == 7, "partial specialization body elaborated");
  __CPROVER_assert(sizeof(b.value) == sizeof(int), "cp member has type int");

  return 0;
}
