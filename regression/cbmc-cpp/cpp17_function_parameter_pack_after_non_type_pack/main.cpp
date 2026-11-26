// N5008 [temp.deduct.call]/1, [temp.variadic]/5: in
// `template <unsigned long... Js, class... Ls> int d(seq<Js...>, Ls... ls)'
// Js is deduced from seq<1, 2> and Ls from the trailing arguments; the
// function parameter pack ls has as many parameters as Ls has elements
// (one here), not as many as the first pack Js.  The body's
// `c(Js, ls...)...' expands over Js with the (possibly empty) ls...
// nested in each element.  libc++'s __make_fmatrix_impl (std::visit) has
// this shape.
extern "C" void __CPROVER_assert(bool, const char *);

template <unsigned long... I>
struct seq
{
};

template <class... Fs>
constexpr int sum(Fs... fs)
{
  return (0 + ... + fs);
}

template <class... Ls>
constexpr int c(Ls... ls)
{
  return sum(ls...);
}

template <unsigned long... Js, class... Ls>
constexpr int d(seq<Js...>, Ls... ls)
{
  return sum(c(Js, ls...)...);
}

template <unsigned long... Is>
constexpr int h(seq<Is...>)
{
  return (100 + ... + Is);
}

template <unsigned long... Is, unsigned long... Js>
constexpr int b(seq<Is...>, seq<Js...>)
{
  return sum(h(seq<Is..., Js>{})...);
}

int main()
{
  __CPROVER_assert(d(seq<1, 2>{}) == 3, "empty ls");
  __CPROVER_assert(d(seq<1, 2>{}, 10) == 23, "one ls");
  __CPROVER_assert(b(seq<5>{}, seq<0, 1, 2>{}) == 318, "nested expansion");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
