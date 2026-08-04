// N5008 [temp.names]/9 + [temp.constr.atomic]/3: a concept-id is a
// prvalue of type bool; if substituting its template arguments yields
// an invalid type or expression the constraint is NOT SATISFIED --
// the concept-id evaluates to false, it is not an error.  libc++'s
// common_reference_with<_Tp, _Up> evaluates
// same_as<_Tp, common_reference_t<_Tp, _Up>> for types with no
// common_reference<...>::type; CBMC hard-errored ("found no match for
// symbol 'same_as'"), killing the whole <vector>/<map>/<string>
// conversion (cvise-reduced from the vector driver, archived as
// .kiro/reductions/vector_same_as_cvt2_50lines.cpp).
extern "C" void __CPROVER_assert(bool, const char *);
template <class, class> concept same_as = true;
template <class> struct common_reference;
template <class... _Types>
using common_reference_t = common_reference<_Types...>::type;
template <class _Up>
concept common_reference_with = same_as<_Up, common_reference_t<_Up>>;
template <bool, class _If, class _Else> struct cond { using type = _Else; };
template <class I, class E> struct cond<true, I, E> { using type = I; };
struct A {}; struct B {};
using r = cond<common_reference_with<int>, A, B>::type;
int main() {
  __CPROVER_assert(sizeof(r) == sizeof(B), "unsatisfied concept picks else");
  return 0;
}
