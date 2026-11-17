// N5008 [temp.mem]/1, [temp.pre]/1: a member class template of a class
// template defined outside the class has two template-heads; with a
// requires-clause in the first, `template <class V> requires small<V>
// template <bool Const> class view<V>::iterator { ... }', Const is still
// the member template's parameter.  The outer head replaced the inner one
// ("symbol 'Const' is unknown"); libc++'s transform_view::__iterator is
// defined this way.  The associated constraints are the conjunction of
// both requires-clauses ([temp.constr.decl]/3).
extern "C" void __CPROVER_assert(bool, const char *);

template <bool B, class T>
struct maybe_const
{
  using type = T;
};

template <class T>
concept small = sizeof(T) <= 8;

template <class V>
  requires small<V>
struct view
{
  template <bool>
  class iterator;
  iterator<false> begin()
  {
    return {v};
  }
  iterator<true> cbegin()
  {
    return {v};
  }
  V v;
};

template <class V>
  requires small<V>
template <bool Const>
class view<V>::iterator
{
  using Base = typename maybe_const<Const, V>::type;

public:
  Base cur;
  Base get() const
  {
    return cur + (Const ? 1 : 0);
  }
};

int main()
{
  view<int> w{3};
  __CPROVER_assert(w.begin().get() == 3, "Const = false");
  __CPROVER_assert(w.cbegin().get() == 4, "Const = true");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
