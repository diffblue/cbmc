extern "C" void __CPROVER_assert(bool, const char *);
template <class _Buf, class _Tp, class _Alloc>
struct layoutt
{
  _Tp *__end_;
  void __relocate(_Tp *&__first, _Tp *&__last)
  {
    __end_ = __last;
    __first = nullptr;
    __last = nullptr;
  }
};
template <class _Tp, class _Alloc, template <class, class, class> class _Layout>
class buft : _Layout<buft<_Tp, _Alloc, _Layout>, _Tp, _Alloc>
{
  // class default: the base is PRIVATE ([class.access.base]/2).
public:
  using __base_type = _Layout<buft, _Tp, _Alloc>;
  // [namespace.udecl]/16,19: the member is republished PUBLIC; a call
  // on a buft lvalue adjusts the implicit object argument to the
  // (privately inherited) base.
  using __base_type::__relocate;
  _Tp *end()
  {
    return this->__end_;
  }
};
int main()
{
  buft<int, char, layoutt> b;
  int x, y;
  int *first = &x;
  int *last = &y;
  b.__relocate(first, last);
  __CPROVER_assert(
    b.end() == &y && first == nullptr && last == nullptr,
    "using-declared member of private TT base");
  return 0;
}
