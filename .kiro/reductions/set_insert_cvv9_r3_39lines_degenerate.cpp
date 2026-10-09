template <class> struct pointer_traits;
template <class _Tp> struct pointer_traits<_Tp *> {
  typedef _Tp element_type;
  template <class _Up> using rebind = _Up *;
};
template <class _From, class _To>
using __rebind_pointer_t = pointer_traits<_From>::template rebind<_To>;
struct less {
  void operator()(int &__x, int) { __x; }
};
template <class, class> struct __tree_node {
  int __value_;
};
template <class _NodePtr, class = pointer_traits<_NodePtr>::element_type>
struct __tree_node_types;
template <class _NodePtr, class _Tp, class _VoidPtr>
struct __tree_node_types<_NodePtr, __tree_node<_Tp, _VoidPtr>> {
  typedef _NodePtr __node_pointer;
};
void __find_equal() {}
struct {
  void __insert_unique() {
    __tree_node_types<__rebind_pointer_t<void *, __tree_node<int, void>>>
        __parent;
    __find_equal();
  }
  void __count_unique() {
    int __k;
    __tree_node_types<__rebind_pointer_t<void *, __tree_node<int, void>>>::
        __node_pointer __rt;
    less __trans_tmp_4;
    __trans_tmp_4(__rt->__value_, 0);
  }
} __tree_;
void insert() { __tree_.__insert_unique(); }
int main() {
  insert();
  __tree_.__count_unique();
}
