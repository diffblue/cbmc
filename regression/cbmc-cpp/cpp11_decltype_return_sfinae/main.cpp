// Complete pattern from libc++-20's __unwrap_iter:
// - decltype return type
// - default type template parameter
// - SFINAE non-type default parameter
// - qualified call from a different template

namespace std {
  template<class T> T&& declval() noexcept;
}

template<bool B, class T = void> struct enable_if {};
template<class T> struct enable_if<true, T> { typedef T type; };
template<bool B, class T = void>
using enable_if_t = typename enable_if<B, T>::type;

template<class T> struct is_copy_constructible {
  static constexpr bool value = true;
};

namespace ns {

template<class Iter>
struct unwrap_impl {
  static Iter unwrap(Iter i) { return i; }
};

template<class Iter,
         class Impl = unwrap_impl<Iter>,
         enable_if_t<is_copy_constructible<Iter>::value, int> = 0>
decltype(Impl::unwrap(std::declval<Iter>()))
unwrap(Iter i) {
  return Impl::unwrap(i);
}

template<class Iter>
void do_sort(Iter first, Iter last) {
  auto f = ns::unwrap(first);
  auto l = ns::unwrap(last);
  (void)f; (void)l;
}

} // namespace ns

int main() {
  int arr[] = {3, 1, 2};
  ns::do_sort(arr + 0, arr + 3);
  __CPROVER_assert(arr[0] == 3, "not sorted");
}
