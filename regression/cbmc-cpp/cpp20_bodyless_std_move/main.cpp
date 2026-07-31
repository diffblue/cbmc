// cvise-reduced from a preprocessed libc++ <vector> push_back driver
// (the whole vector-semantic KNOWNBUG family: size() reads garbage
// after push_back).  A call to a DECLARED-ONLY std::move -- which
// clang guarantees to link and behave as the [forward]/4 cast via its
// builtin-std-move treatment -- is modelled by CBMC as an
// unconstrained bodyless call: the returned reference is NULL/garbage
// and everything assigned through it is nondet.  Per N5008
// [forward]/4, std::move(t) is exactly
// static_cast<remove_reference_t<T>&&>(t).
// clang++/valgrind run the program clean.
extern "C" void __CPROVER_assert(bool, const char *);

namespace std {
inline namespace {
template <class _Tp> _Tp move(_Tp &&);
int __end_;
struct vector {
  long size() { return __end_; }
  void push_back() {
    __end_++;
    __end_ = move(__end_);
  }
};
} // namespace
} // namespace std
int main() {
  std::vector v;
  v.push_back();
  __CPROVER_assert(v.size(), "one size");
}
