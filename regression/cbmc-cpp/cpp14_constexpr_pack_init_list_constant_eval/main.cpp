// N5008 [expr.const], [temp.inst]/5, [temp.variadic]/5: constant evaluation
// of a constexpr function template with a pack-initialised local array.
extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;

template <bool B, typename T = void>
struct enable_if
{
};
template <typename T>
struct enable_if<true, T>
{
  typedef T type;
};

template <typename T, typename... Ts>
constexpr size_t find_uniq()
{
  constexpr bool found[sizeof...(Ts)] = {__is_same(T, Ts)...};
  size_t n = sizeof...(Ts);
  for(size_t i = 0; i < sizeof...(Ts); ++i)
    if(found[i])
    {
      if(n < sizeof...(Ts))
        return sizeof...(Ts);
      n = i;
    }
  return n;
}

template <typename T, typename... Ts>
constexpr size_t wrap()
{
  return find_uniq<T, Ts...>();
}

template <
  typename T,
  typename = typename enable_if<(find_uniq<T, int, double>() < 2)>::type>
int only_alternatives(T)
{
  return 4;
}

template <typename T, size_t V = find_uniq<T, int, double>()>
size_t as_default(T)
{
  return V;
}

template <size_t N>
struct value
{
  static const size_t v = N;
};

int main()
{
  // run-time use first: the specialization's definition is queued
  size_t r = wrap<double, int, double>();
  __CPROVER_assert(r == 1, "runtime");
  // ... then required as a constant
  constexpr size_t c = wrap<double, int, double>();
  __CPROVER_assert(c == 1, "constexpr after runtime use");
  static_assert(wrap<double, int, double>() == 1, "static_assert");
  static_assert(find_uniq<char, int, double>() == 2, "absent");
  static_assert(find_uniq<double, int, double, double>() == 3, "twice");
  __CPROVER_assert(value<find_uniq<int, int, double>()>::v == 0, "targ");
  __CPROVER_assert(only_alternatives(1.5) == 4, "enable_if default");
  __CPROVER_assert(as_default(1.5) == 1, "non-type default");
  return 0;
}
