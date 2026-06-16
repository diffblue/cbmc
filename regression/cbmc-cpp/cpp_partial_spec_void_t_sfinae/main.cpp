// CORE (N5008 [temp.spec.partial.match]/2, [temp.deduct]/8).
//
// Classic `void_t` partial-specialization SFINAE, both as a member of a class
// template (`has_mem`) and an expression-`decltype` form (`can_foo`).  CBMC is
// correct here: the specialization is selected when the probed member type /
// expression is well-formed and rejected otherwise -- even in the
// class-member-instantiation context.  This pins the divergence in
// cpp20_partial_spec_conditional_sfinae_member to the *conditional-operator*
// `decltype` specifically, not to `void_t` SFINAE in general.

template <class X>
X declval();

template <class...>
using void_t = void;

template <class T, class = void>
struct has_mem
{
  int tag = 1;
};
template <class T>
struct has_mem<T, void_t<typename T::mem>>
{
  int tag = 2;
};

template <class T, class = void>
struct can_foo
{
  int tag = 1;
};
template <class T>
struct can_foo<T, void_t<decltype(declval<T>().foo())>>
{
  int tag = 2;
};

struct WithMem
{
  using mem = int;
  void foo();
};

template <class T>
struct Outer
{
  has_mem<T> hm;
  can_foo<T> cf;
  int v;
  Outer() : v(7) {}
};

int main()
{
  Outer<int> oi;
  Outer<WithMem> ow;
  __CPROVER_assert(oi.hm.tag == 1, "int: no ::mem -> primary");
  __CPROVER_assert(ow.hm.tag == 2, "WithMem: ::mem -> specialization");
  __CPROVER_assert(oi.cf.tag == 1, "int: no .foo() -> primary");
  __CPROVER_assert(ow.cf.tag == 2, "WithMem: .foo() -> specialization");
  return 0;
}
