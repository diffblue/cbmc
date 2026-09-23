// N5008 [temp.spec.partial.general], [temp.constr.decl]: same-pattern partial
// specializations told apart by their constraints (the __iter_concept shape).
struct rat
{
};
struct fwd
{
};
struct WithConcept
{
  using iterator_concept = fwd;
  using iterator_category = rat;
};
struct WithCategory
{
  using iterator_category = rat;
};
struct Neither
{
};

// the requirements name members of the ITERATOR TYPE itself (or of a pointer
// wrapper), so that an absent member is a substitution failure in the
// immediate context, not an error inside a class template instantiation
template <class I>
struct traits
{
  using type = I;
};
template <class I>
struct traits<I *>
{
  struct type
  {
  };
};
template <class I>
using traits_t = typename traits<I>::type;

template <class I>
struct impl;

template <class I>
requires requires
{
  typename traits_t<I>::iterator_concept;
}
struct impl<I>
{
  using type = typename traits_t<I>::iterator_concept;
};

template <class I>
requires(
  !requires { typename traits_t<I>::iterator_concept; } &&
  requires { typename traits_t<I>::iterator_category; }) struct impl<I>
{
  using type = typename traits_t<I>::iterator_category;
};

template <class I>
requires(
  !requires { typename traits_t<I>::iterator_concept; } &&
  !requires { typename traits_t<I>::iterator_category; }) struct impl<I>
{
  using type = rat;
};

template <class I>
struct impl
{
};

template <class I>
using concept_t = typename impl<I>::type;

int main()
{
  static_assert(__is_same(concept_t<WithConcept>, fwd), "iterator_concept");
  static_assert(__is_same(concept_t<WithCategory>, rat), "iterator_category");
  static_assert(__is_same(concept_t<int *>, rat), "pointer: default");
  return 0;
}
