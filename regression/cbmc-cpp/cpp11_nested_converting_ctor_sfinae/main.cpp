// Nested converting-constructor SFINAE across two distinct class types.
//
// Converting an argument to `opt<Wrap>` selects `opt`'s converting constructor
// template, whose viability is gated by a constraint that queries
// `is_constructible<Wrap, U>` (here modelled with the `__is_constructible`
// builtin behind a variable template, exactly as libstdc++'s
// `std::optional`/`std::unique_ptr` do).  Evaluating that constraint requires,
// in turn, a conversion of `U` to `Wrap` through `Wrap`'s own converting
// *template* constructor.
//
// N5008 [over.ics.user]: a user-defined conversion sequence contains at most
// one user-defined conversion, but a nested `is_constructible` query about a
// *different* target type is a separate sequence and must be evaluated on its
// own merits.  The front-end guarded its converting-template-constructor
// fallback with a single global boolean ("in a template conversion"), which
// blocked the legitimate nested conversion to `Wrap` while converting to
// `opt<Wrap>`; the constraint then wrongly evaluated to false and every
// `opt<Wrap>` constructor was rejected ("found no match for symbol 'opt'").
// This is exactly how `std::optional<std::reference_wrapper<const T>>(x)`
// failed to compile (e.g. in src/util/simplify_utils.cpp).

template<bool B, class T = void>
struct en
{
};
template<class T>
struct en<true, T>
{
  using type = T;
};

template<class A, class B>
constexpr bool ic_v = __is_constructible(A, B);

struct Wrap
{
  int v;
  template<class U>
  Wrap(U &&u) : v((int)u)
  {
  }
};

template<class Tp>
struct opt
{
  Tp storage;
  int tag;
  template<class Up = Tp, typename en<ic_v<Tp, Up>, bool>::type = true>
  opt(Up &&u) : storage(static_cast<Up &&>(u)), tag(7)
  {
  }
};

int main()
{
  int x = 5;
  opt<Wrap> o(x);
  __CPROVER_assert(o.tag == 7, "nested converting ctor was selected");
  __CPROVER_assert(o.storage.v == 5, "wrapped value is correct");
  __CPROVER_assert(o.storage.v == 6, "WRONG: must fail");
  return 0;
}
