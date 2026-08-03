// TWO heterogeneous elements in a base-specifier pack expansion with
// a parallel mem-initializer pack (`impl(T... u) : leaf<T>(u)...`,
// N5008 [temp.variadic]/5 -- the base list and the mem-initializer
// list expand in lockstep).  The single-element case and the
// libc++ __tuple_impl partial-specialization shape are FIXED
// (cpp11_tuple_leaf_no_body); with two elements the constructor's
// mem-initializer still reports "found no match for symbol 'leaf'"
// and the instance body is dropped.  g++/clang++ run clean.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T> struct leaf {
  T v;
  leaf(T u) : v(u) {}
};
template <class... T> struct impl : leaf<T>... {
  impl(T... u) : leaf<T>(u)... {}
};
int main() {
  impl<int, char> b(42, 'x');
  __CPROVER_assert(static_cast<leaf<int> &>(b).v == 42, "leaf int");
  __CPROVER_assert(static_cast<leaf<char> &>(b).v == 'x', "leaf char");
}
