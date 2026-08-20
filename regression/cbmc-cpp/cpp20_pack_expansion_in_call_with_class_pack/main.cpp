// N5008 [temp.variadic]/5: two pack expansions in one call argument list
// -- the member's own function parameter pack and the ENCLOSING CLASS
// template's non-type pack -- must expand independently:
// `Op()(static_cast<A&&>(a)..., get<Ip>(bound_)...)`, the libc++
// __perfect_forward / __bind_back_op shape behind the ranges pipe.
// CBMC mis-converts the constructor's mem-initializer for the
// pack-typed member ("invalid implicit conversion from 'signed int' to
// 'struct tup'"), so the constructor body is dropped and the bound value
// reads garbage.  The FOLD form of the same shape is fixed
// (cpp20_fold_over_class_pack_in_member); this is the call-argument
// expansion form.
// g++ and clang++ both accept and run clean.
extern "C" void __CPROVER_assert(bool, const char *);
template <unsigned long...> struct iseq
{
};
template <class T> struct tup
{
  T v_;
};
template <int I, class T> T get(tup<T> t)
{
  return t.v_;
}
// bound args held in a BASE subobject (libc++ __perfect_forward shape)
template <class Op, class Seq, class... B> struct pf_impl;
template <class Op, unsigned long... Ip, class... B>
struct pf_impl<Op, iseq<Ip...>, B...>
{
  tup<B...> bound_;
  pf_impl(B... b) : bound_{b...}
  {
  }
  template <class... A> auto operator()(A &&...a)
  {
    return Op()(static_cast<A &&>(a)..., get<Ip>(bound_)...);
  }
};

struct taker
{
  int operator()(int (&arr)[1], int n)
  {
    return arr[0] + n;
  }
};
int main()
{
  int arr[1]{5};
  pf_impl<taker, iseq<0>, int> c(3);
  __CPROVER_assert(c(arr) == 8, "base-held bound args expansion");
  return 0;
}
