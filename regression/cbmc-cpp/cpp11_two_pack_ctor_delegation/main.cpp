// The remaining layer of cpp11_tuple_leaf_no_body, header-free: a
// member constructor template with TWO parameter packs (a non-type
// index pack and a trailing type pack), called from ANOTHER
// constructor template's mem-initializer delegation, fails argument
// deduction: "found no match for symbol 'impl'".  A direct call from
// main deduces fine; the delegation from an instantiated ctor
// template is required.  g++/clang++/valgrind run clean.

extern "C" void __CPROVER_assert(bool, const char *);
template <unsigned long...> struct indices {};
struct impl {
  int v_;
  template <unsigned long... Uf, class... Up>
  impl(indices<Uf...>, Up... u) : v_(0) {
    int arr[] = {(v_ = u)...};
    (void)arr;
  }
};
struct tup {
  impl base_;
  template <class... Up> tup(Up... u) : base_(indices<0>(), u...) {}
};
int main() {
  tup t(42);
  __CPROVER_assert(t.base_.v_ == 42, "two-pack delegation");
  return 0;
}
