// N5008 [temp.deduct.call]/1, [temp.variadic]/5: `get<0>(tup<int, char>())'
// deduces T = {int, char}, and the specialization get<0, int, char> is the
// one called.  Inside a namespace-scope alias's decltype (and so in a
// member's trailing return type checked from one) CBMC instantiated
// get<0, int>, whose parameter tup<int> rejected the argument, and the alias
// was dropped ("symbol 'R1' is unknown").  libc++'s
// __perfect_forward_impl::operator() (`decltype(_Op()(get<_Idx>(
// __bound_args_)...))') failed this way under std::invoke_result_t.
extern "C" void __CPROVER_assert(bool, const char *);

template <class... T>
struct tup
{
};

template <unsigned long N, class... T>
int get(tup<T...>);

template <class... T>
int count(tup<T...>)
{
  return sizeof...(T);
}

struct holder
{
  tup<int, char> bound;
  auto f() -> decltype(get<0>(bound));
};

using R1 = decltype(get<0>(tup<int, char>()));
using R2 = decltype(holder().f());
using R3 = decltype(count(tup<int, char, long>()));

int main()
{
  __CPROVER_assert(__is_same(R1, int), "explicit argument and a pack");
  __CPROVER_assert(__is_same(R2, int), "member trailing return type");
  __CPROVER_assert(__is_same(R3, int), "deduced pack");
  __CPROVER_assert(count(tup<int, char, long>()) == 3, "call");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
