// N5008 [meta.unary.prop]/9: is_constructible<T, Args...> holds iff
// `T t(declval<Args>()...);' is well-formed; with several Args that is
// direct-initialization by a constructor ([dcl.init.general]/16.6.2), and
// an lvalue-reference Arg gives an lvalue argument.  CBMC compared only the
// first argument type, so __is_constructible was false for every
// two-argument constructor (libc++'s tuple and __perfect_forward_impl are
// constrained this way).
extern "C" void __CPROVER_assert(bool, const char *);

struct two
{
  two(int, char)
  {
  }
};

struct ref
{
  ref(int &, int)
  {
  }
};

template <class T, class... A>
constexpr bool constructible = __is_constructible(T, A...);

static_assert(__is_constructible(two, int, char));
static_assert(__is_constructible(two, int &&, const char &));
static_assert(!__is_constructible(two, int, char, int));
static_assert(!__is_constructible(two, int));
static_assert(__is_constructible(ref, int &, int));
static_assert(!__is_constructible(ref, int &&, int));
static_assert(!__is_constructible(int, int, int));
static_assert(constructible<two, int, char>);
static_assert(!constructible<ref, int, int>);

int main()
{
  __CPROVER_assert(constructible<two, long, char>, "pack expansion");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
