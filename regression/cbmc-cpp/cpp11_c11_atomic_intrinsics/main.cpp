extern "C" void __CPROVER_assert(bool, const char *);
// Clang's __c11_atomic_* intrinsics, as libc++'s <atomic> uses them
// (__cxx_atomic_load/store/exchange/fetch_add in
// <__atomic/cxx_atomic_impl.h>).  Clang only allows them to be called
// directly (not to have their address taken).
template <class T>
struct atomic_impl
{
  _Atomic(T) value;
};
template <class T>
T atomic_load(const atomic_impl<T> *a, int order)
{
  using ptr_type = _Atomic(T) *;
  return __c11_atomic_load(const_cast<ptr_type>(&a->value), order);
}
template <class T>
void atomic_store(atomic_impl<T> *a, T v, int order)
{
  __c11_atomic_store(&a->value, v, order);
}
template <class T>
T atomic_exchange(atomic_impl<T> *a, T v, int order)
{
  return __c11_atomic_exchange(&a->value, v, order);
}
template <class T>
T atomic_fetch_add(atomic_impl<T> *a, T v, int order)
{
  return __c11_atomic_fetch_add(&a->value, v, order);
}
int main()
{
  __c11_atomic_thread_fence(5);
  __c11_atomic_signal_fence(5);
  atomic_impl<int> a;
  atomic_store(&a, 5, 5);
  __CPROVER_assert(atomic_load(&a, 5) == 5, "store then load");
  __CPROVER_assert(
    atomic_exchange(&a, 7, 5) == 5 && atomic_load(&a, 5) == 7,
    "exchange returns the old value");
  __CPROVER_assert(
    atomic_fetch_add(&a, 3, 5) == 7 && atomic_load(&a, 5) == 10, "fetch_add");
  atomic_impl<bool> b;
  atomic_store(&b, true, 5);
  __CPROVER_assert(atomic_load(&b, 5), "bool");
  __CPROVER_assert(atomic_load(&a, 5) == 11, "WRONG (must FAIL)");
}
