// N5008 [namespace.udecl]/1, [temp.variadic]/5.4: pack expansion in a
// using-declaration (the std::variant _Build_FUNs overload-set builder).
extern "C" void __CPROVER_assert(bool, const char *);

template <unsigned long N>
struct ic
{
  static constexpr unsigned long value = N;
};

template <unsigned long I, typename Ti>
struct B
{
  static ic<I> fun(Ti);
};

template <typename... Ti>
struct V;

template <unsigned long... I>
struct iseq
{
};

template <typename Var, typename = iseq<0, 1>>
struct Bs;

template <typename... Ti, unsigned long... I>
struct Bs<V<Ti...>, iseq<I...>> : B<I, Ti>...
{
  using B<I, Ti>::fun...;
};

template <typename T>
T &&declval();

int main()
{
  __CPROVER_assert(
    decltype(Bs<V<int, double>>::fun(declval<int>()))::value == 0, "int");
  __CPROVER_assert(
    decltype(Bs<V<int, double>>::fun(declval<double>()))::value == 1, "double");
  __CPROVER_assert(decltype(Bs<V<int, double>>::fun(1.5))::value == 1, "lit");
  return 0;
}
