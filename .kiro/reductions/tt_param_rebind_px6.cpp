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
