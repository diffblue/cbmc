extern "C" void __CPROVER_assert(bool, const char *);
namespace outer
{
inline namespace inner
{
template <class _Tp, class _Alloc, class _Buf>
struct layoutt
{
  _Tp *__end_;
  void __set_sentinel(_Tp *__new_end)
  {
    __end_ = __new_end;
  }
  void __set_sentinel(unsigned long __new_size)
  {
    __end_ = nullptr;
    (void)__new_size;
  }
};
template <class _Tp, class _Alloc,
          template <class, class, class> class _Layout>
struct buft : _Layout<_Tp, _Alloc, buft<_Tp, _Alloc, _Layout>>
{
  using __base_type = _Layout<_Tp, _Alloc, buft>;
  using __base_type::__set_sentinel;
  struct transt
  {
    _Tp *__pos_;
    buft *__parent_;
    ~transt()
    {
      __parent_->__set_sentinel(__pos_);
    }
  };
  void put(_Tp *p)
  {
    transt tx{p, this};
  }
};
namespace detail
{
inline void run()
{
  buft<int, char, layoutt> b;
  int x;
  b.__end_ = nullptr;
  b.put(&x);
  __CPROVER_assert(
    b.__end_ == &x, "TT-param base resolved through namespace-nested template");
}
} // namespace detail
} // namespace inner
} // namespace outer
int main()
{
  outer::detail::run();
  return 0;
}
