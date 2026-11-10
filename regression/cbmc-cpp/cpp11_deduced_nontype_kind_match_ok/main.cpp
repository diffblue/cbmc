// N5008 [temp.deduct.type]/20: the accepting cases.
extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;

template <unsigned long...>
struct indices
{
};
template <size_t... I>
struct iseq
{
};
enum E
{
  A,
  B
};
template <E... es>
struct es_t
{
};
template <int i>
class Ai
{
};
template <const short cs>
class Bs
{
};

struct impl
{
  int n;
  template <unsigned long... U>
  impl(indices<U...>) : n(sizeof...(U))
  {
  }
  template <size_t... U>
  impl(iseq<U...>) : n(10 + sizeof...(U))
  {
  }
  template <E... es>
  impl(es_t<es...>) : n(20 + sizeof...(es))
  {
  }
};

template <short s>
int f(Ai<s>)
{
  return s;
}
template <short s>
int g(Bs<s>)
{
  return s;
}

int main()
{
  impl a(indices<0ul, 1ul>{});
  __CPROVER_assert(a.n == 2, "same type");
  impl b(iseq<0, 1, 2>{});
  __CPROVER_assert(b.n == 13, "same type through a typedef");
  impl c(es_t<A, B>{});
  __CPROVER_assert(c.n == 22, "enumeration");
  Ai<1> ai;
  __CPROVER_assert(f<1>(ai) == 1, "explicitly specified: not deduced");
  Bs<1> bs;
  __CPROVER_assert(g(bs) == 1, "cv-qualifiers are ignored");
  return 0;
}
