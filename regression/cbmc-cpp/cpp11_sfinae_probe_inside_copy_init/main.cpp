// A SFINAE probe that runs while a copy-initialization explores the
// constructors of its target class must see the full set of implicit
// conversions again.
//
// N5008 [over.best.ics.general]/4 suppresses user-defined conversion
// sequences only for the parameters of the constructor candidates of the ONE
// copy-initialization being resolved.  Deducing a constructor template among
// those candidates and substituting its constrained default template argument
// ([temp.deduct.general]/5) runs separate overload resolutions
// ([temp.deduct]/8, the immediate context); their conversions -- here a
// derived-to-base copy-initialization, a standard conversion per
// [over.best.ics.general]/6 -- are unaffected.
//
// This is the libstdc++ 11 shape: `basic_string(_InputIterator,
// _InputIterator)` constrained by `_RequireInputIter`, whose
// `is_convertible<random_access_iterator_tag, input_iterator_tag>` is the
// SFINAE-based helper (`__test_aux<_To1>(declval<_From1>())`).  A
// `const char*` -> `basic_string` conversion probe used to evaluate the trait
// as false, and its class instance -- cached without its `value` member --
// then broke every later `std::vector<int> v(first, last)`.

extern "C" void __CPROVER_assert(bool, const char *);

template <bool B, class T = void> struct enable_if { };
template <class T> struct enable_if<true, T> { typedef T type; };
template <bool B, class T = void> using enable_if_t = typename enable_if<B, T>::type;
template <class T> T &&declval() noexcept;
struct true_type { static const bool value = true; };
struct false_type { static const bool value = false; };

template <class From, class To>
class is_convertible_helper
{
  template <class To1> static void test_aux(To1) noexcept;
  template <class From1, class To1, class = decltype(test_aux<To1>(declval<From1>()))>
  static true_type test(int);
  template <class, class> static false_type test(...);
public:
  typedef decltype(test<From, To>(0)) type;
};
template <class From, class To> struct is_convertible : is_convertible_helper<From, To>::type { };

struct input_iterator_tag { };
struct forward_iterator_tag : input_iterator_tag { };
struct random_access_iterator_tag : forward_iterator_tag { };

template <class It> struct iterator_traits { using iterator_category = typename It::iterator_category; };
template <class T> struct iterator_traits<T *> { using iterator_category = random_access_iterator_tag; };
template <class It>
using RequireInputIter = enable_if_t<is_convertible<typename iterator_traits<It>::iterator_category, input_iterator_tag>::value>;

template <class C> struct alloc { typedef C value_type; };
template <class A> using RequireAllocator = typename A::value_type;

template <class C, class A = alloc<C>> struct basic_str
{
  int n;
  basic_str() : n(0) { }
  basic_str(const basic_str &o) : n(o.n) { }
  basic_str(basic_str &&o) : n(o.n) { }
  // like libstdc++'s CTAD-guarded `basic_string(const _CharT*, const _Alloc&)`
  // (LWG 3076): a constructor TEMPLATE, so the conversion probe below goes
  // through constructor-template deduction
  template <class = RequireAllocator<A>>
  basic_str(const C *p, const A & = A()) : n(0)
  {
    while(p[n] != 0)
      n++;
  }
  // range constructor: deducing it during the `const char*` -> str probe
  // below evaluates RequireInputIter<const char*>, i.e. the trait above
  template <class I, class = RequireInputIter<I>>
  basic_str(I a, I b, const A & = A()) : n(b - a) { }
};
using str = basic_str<char>;

// probe context: binding `const str&` to a `const char*` argument is a
// copy-initialization that explores str's constructors ([over.match.copy]);
// the range constructor template is among the candidates deduced
inline int length(const str &s) { return s.n; }
inline int probe() { return length("ab"); }

struct vec
{
  int n;
  template <class I, class = RequireInputIter<I>> vec(I a, I b) : n(b - a) { }
};

int main()
{
  int arr[3] = {1, 2, 3};
  __CPROVER_assert(probe() == 2, "const char* converted through str(const char*)");
  // the trait must still be true after the probe
  __CPROVER_assert(is_convertible<random_access_iterator_tag, input_iterator_tag>::value, "derived-to-base is convertible");
  vec v(arr, arr + 3);
  __CPROVER_assert(v.n == 3, "range constructor of a later class uses the same trait instance");
  int *p = arr;
  vec w(p, p + 2);
  __CPROVER_assert(w.n == 2, "pointer arguments");
  return 0;
}
