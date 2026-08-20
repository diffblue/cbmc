// N5008 [expr.prim.fold]/1-2: a fold expression's pack is the one its
// PATTERN names.  Here the fold `(0 + ... + get<_Ip>(bound_))` inside a
// member function template folds over the ENCLOSING CLASS template's
// non-type pack `_Ip` while the member has its own pack `A` -- the
// libc++ __bind_back_op / __perfect_forward shape.  The member-body fold
// expander previously sized the pack only from replicated FUNCTION
// parameters or from a unique pack_size_map entry, so with both packs
// live the fold was left unexpanded ("unexpected expression:
// cpp_binary_fold") and the whole member body was dropped.
extern "C" void __CPROVER_assert(bool, const char *);
template <unsigned long...> struct iseq
{
};
template <class... T> struct tup
{
  int n_;
  tup(T... t) : n_(sizeof...(T))
  {
  }
};
template <unsigned long I, class... T> int get(tup<T...> t)
{
  return t.n_;
}
template <class Seq, class... B> struct pf;
template <unsigned long... Ip, class... B> struct pf<iseq<Ip...>, B...>
{
  tup<B...> bound_;
  pf(B... b) : bound_(b...)
  {
  }
  template <class... A> int call(A &&...a)
  {
    return (0 + ... + get<Ip>(bound_));
  }
};
int main()
{
  pf<iseq<0>, int> p(3);
  __CPROVER_assert(p.call() == 1, "mem-init in multi-pack partial spec");
  return 0;
}
