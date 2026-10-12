// N5008 [temp.variadic]/5: a pack name is expanded by the innermost pack
// expansion that contains it.  In `sum(one(seq<Js>{}, ls...)...)' the outer
// expansion is over the template parameter pack Js; the function parameter
// pack ls is expanded inside each element; likewise `seq<Is..., Js>' in a
// pattern over Js expands Is itself.  The front end expanded the outer
// pattern over ls or over Is (so the instances of `one' got Js's first
// element only, or the expansion was dropped for an empty Is), and with an
// empty ls left `ls' unexpanded ("symbol 'ls' is unknown").  libc++'s
// variant visitation (__make_fmatrix_impl) has this shape.
extern "C" void __CPROVER_assert(bool, const char *);

template <unsigned long... I>
struct seq
{
};
template <class... T>
int sum(T... t)
{
  return (0 + ... + t);
}
template <unsigned long J, class... L>
int one(seq<J>, L... ls)
{
  return J * 10 + sum(ls...);
}
template <unsigned long... Js, class... Ls>
int outer(seq<Js...>, Ls... ls)
{
  return sum(one(seq<Js>{}, ls...)...);
}
template <unsigned long... I>
struct counted
{
  static constexpr unsigned long n = sizeof...(I);
};
template <unsigned long... Is, unsigned long... Js>
unsigned long counts(seq<Is...>, seq<Js...>)
{
  return sum(counted<Is..., Js>::n...);
}
struct holder
{
  template <unsigned long... Js, class... Ls>
  static int outer(seq<Js...>, Ls... ls)
  {
    return sum(one(seq<Js>{}, ls...)...);
  }
};

int main()
{
  __CPROVER_assert(outer(seq<1, 2>{}, 3, 4) == 17 + 27, "two and two");
  __CPROVER_assert(outer(seq<1, 2, 3>{}, 3, 4) == 60 + 21, "three and two");
  __CPROVER_assert(outer(seq<5>{}) == 50, "empty inner pack");
  __CPROVER_assert(holder::outer(seq<1, 2>{}, 3) == 13 + 23, "member");
  __CPROVER_assert(holder::outer(seq<5>{}) == 50, "member, empty inner pack");
  __CPROVER_assert(counts(seq<>{}, seq<1, 2>{}) == 2, "empty inner pack");
  __CPROVER_assert(counts(seq<7>{}, seq<1, 2>{}) == 4, "template arguments");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
