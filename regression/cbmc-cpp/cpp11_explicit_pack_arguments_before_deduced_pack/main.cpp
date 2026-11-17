// N5008 [temp.arg.explicit]/4, /9, [temp.deduct.call]/1: explicitly
// specified template arguments for a template parameter pack that is
// followed by another (deduced) pack: in `g<char>(seq<4>{})' Vs = {char}
// and Is = {4} is deduced from the argument ([temp.arg.explicit]/6: from the
// first pack on, every explicit argument belongs to that pack).  libc++'s
// variant visitation calls __make_fmatrix_impl<_Fp, _Vs...>(
// index_sequence<>{}, ...) with this shape.
extern "C" void __CPROVER_assert(bool, const char *);

template <unsigned long... I>
struct seq
{
};

template <class... Vs, unsigned long... Is>
int g(seq<Is...>)
{
  return sizeof...(Vs) * 100 + sizeof...(Is);
}

template <class F, class... Vs, unsigned long... Is>
int f(seq<Is...>)
{
  return sizeof...(Vs) * 100 + sizeof...(Is);
}

struct base
{
  template <
    class F,
    class... Vs,
    unsigned long... Is,
    unsigned long... Js,
    class... Ls>
  static int impl(seq<Is...>, seq<Js...>, Ls...)
  {
    return sizeof...(Vs) * 100 + sizeof...(Js) * 10 + sizeof...(Ls);
  }
};

int main()
{
  __CPROVER_assert(g<char>(seq<4>{}) == 101, "leading pack");
  __CPROVER_assert(f<int, char, long>(seq<4, 5>{}) == 202, "after a type");
  __CPROVER_assert(
    base::impl<int, char>(seq<>{}, seq<0, 1>{}) == 120, "several packs");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
