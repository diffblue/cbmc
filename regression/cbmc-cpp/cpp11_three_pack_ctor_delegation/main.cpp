// The next layer above cpp11_two_pack_ctor_delegation, header-free: a
// member constructor template with THREE parameter packs (a non-type
// index pack, a middle type pack, and a trailing function parameter
// pack) plus interleaved EMPTY-specialization parameters, called from
// another constructor template's mem-initializer delegation -- exactly
// libc++'s __tuple_impl constructor shape.  Deduction recorded the
// trailing pack's arity as zero, the instance was built with the pack
// expanded to ZERO parameters, and the call found no match
// ([temp.deduct.call]/1, [temp.variadic]/4).  g++/clang++ run clean.
extern "C" void __CPROVER_assert(bool, const char *);
template <unsigned long...>
struct indices
{
};
template <class...>
struct types
{
};
struct impl
{
  int v_;
  template <unsigned long... Uf, class... Tf, class... Up>
  impl(indices<Uf...>, types<Tf...>, indices<>, types<>, Up... u) : v_(0)
  {
    int arr[] = {(v_ = u)...};
    (void)arr;
  }
};
struct tup
{
  impl base_;
  template <class... Up>
  tup(Up... u)
    : base_(indices<0>(), types<Up...>(), indices<>(), types<>(), u...)
  {
  }
};
int main()
{
  tup t(42);
  __CPROVER_assert(t.base_.v_ == 42, "three-pack delegation");
  return 0;
}
