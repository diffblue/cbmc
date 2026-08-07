// N5008 [temp.deduct.type]/8 (P has the form TT<T>): the
// template-template-parameter is deduced to the TEMPLATE the argument
// was instantiated from, NOT to the argument instance.  CBMC binds the
// INSTANCE type, so every body use of the parameter (`_Alloc<_Up>`)
// resolves to that one instance regardless of its own arguments:
// R<allocator<int>, char>::type comes out allocator<int> (u is 4
// bytes, not 1).  This is libc++/libstdc++'s allocator_traits rebind
// chain (std::set's __tree::__pair1_ member type; the strict-C++11
// distillation of the cx1 reduction of cpp11_set_insert_libcxx).
//
// A candidate fix (bind template_parameter_symbol_typet of the
// looked-up template symbol, archived in
// .kiro/reductions/tt_param_deduction_fix_regressed.patch) fixes this
// shape but regresses cpp11_libcxx_tuple (make_tuple wrong-code) and
// blows the 256-object ceiling on deque/map tests -- the unification
// of rebind instances was load-bearing for sharing; needs scoped
// rework.
extern "C" void __CPROVER_assert(bool, const char *);
template <class, class> struct R;
template <template <class> class _Alloc, class _Tp, class _Up>
struct R<_Alloc<_Tp>, _Up>
{
  typedef _Alloc<_Up> type;
};
template <class T> struct allocator
{
  T v;
};
int main()
{
  typename R<allocator<int>, char>::type x;
  __CPROVER_assert(sizeof(x.v) == 1, "resolved");
  return 0;
}
