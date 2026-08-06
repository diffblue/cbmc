// N5008 [temp.deduct.type]: deducing against a class-template
// specialization needs only the instance's template ARGUMENTS, not a
// completed definition.  With `__tree_node` only forward-declared,
// the instance tag-__tree_node<int,void> records its argument list
// but no completed template; the partial-specialization pattern
// `__tree_node_types<_NodePtr, __tree_node<_Tp, _VoidPtr>>` (libc++'s
// <__tree>, reached through std::set's __compressed_pair member
// __pair1_) was rejected before argument-wise deduction, its
// parameters stayed unbound, and the whole declaration was dropped
// ("symbol '__pair1_' is unknown").  cvise-reduced from the
// preprocessed libc++ <set> seed (835 bytes -> this).
extern "C" void __CPROVER_assert(bool, const char *);
template <class> struct pointer_traits;
template <class _Tp> struct pointer_traits<_Tp *>
{
  typedef _Tp element_type;
};
template <class, class> struct __tree_node;
template <
  class _NodePtr,
  class = typename pointer_traits<_NodePtr>::element_type>
struct __tree_node_types;
template <class _NodePtr, class _Tp, class _VoidPtr>
struct __tree_node_types<_NodePtr, __tree_node<_Tp, _VoidPtr>>
{
  typedef int __end_node_type;
};
typename __tree_node_types<__tree_node<int, void> *>::__end_node_type
  __pair1_;
int main()
{
  __CPROVER_assert(sizeof(__pair1_) >= 1, "pair1 declared");
  return 0;
}
