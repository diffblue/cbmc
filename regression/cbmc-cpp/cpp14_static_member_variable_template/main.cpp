// N5008 [temp.pre]/1, [temp.spec]/4, [temp.mem]/1: static data member
// templates (std::variant's __exactly_once / __accepted_index shape).
extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;

template <typename T, typename U>
constexpr bool same = __is_same(T, U);

template <size_t N>
struct tag_t
{
};
template <size_t N>
constexpr tag_t<N> tag{};

namespace ns
{
template <size_t N>
constexpr tag_t<N> nstag{};
}

struct N
{
  template <typename T>
  static constexpr bool is_int = __is_same(T, int);
  template <typename T>
  static constexpr bool is_int2 = same<T, int>;
};

template <typename X>
struct S
{
  template <typename T>
  static constexpr bool is_x = __is_same(T, X);
  template <typename T>
  static constexpr bool is_x2 = same<T, X>;
};

template <typename... Types>
struct V
{
  template <typename T>
  static constexpr size_t idx = __is_same(T, int) ? 0 : 1;
  size_t i;
  template <typename Tp>
  constexpr V(Tp &&t) : V(ns::nstag<idx<Tp>>, 0)
  {
  }
  template <size_t Np>
  constexpr explicit V(tag_t<Np>, int) : i(Np)
  {
  }
  template <typename Tp>
  static size_t get()
  {
    return idx<Tp>;
  }
  static size_t get_d()
  {
    return idx<double>;
  }
};

int main()
{
  __CPROVER_assert(!N::is_int<char>, "N char");
  __CPROVER_assert(N::is_int<int>, "N int");
  __CPROVER_assert(N::is_int2<int>, "N int2");
  __CPROVER_assert(!N::is_int2<char>, "N char2");
  __CPROVER_assert(S<int>::is_x<int>, "S int");
  __CPROVER_assert(!S<int>::is_x<char>, "S char");
  __CPROVER_assert(S<int>::is_x2<int>, "S int2");
  __CPROVER_assert(!S<int>::is_x2<char>, "S char2");
  __CPROVER_assert(V<int, double>::idx<double> == 1, "direct");
  __CPROVER_assert(V<int, double>::get_d() == 1, "member fn");
  __CPROVER_assert(V<int, double>::get<double>() == 1, "member fn template");
  V<int, double> v = 42;
  __CPROVER_assert(v.i == 0, "ctor int");
  V<int, double> w = 2.5;
  __CPROVER_assert(w.i == 1, "ctor double");
  return 0;
}
