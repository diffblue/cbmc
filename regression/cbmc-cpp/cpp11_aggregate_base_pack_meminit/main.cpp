// N5008 [class.base.init]/7 + [dcl.init.aggr]: a mem-initializer whose
// id denotes an AGGREGATE base (here `leaf<_Up>{__u}...` expanded per
// [temp.variadic]/5) initializes the base subobject per [dcl.init] --
// there is no constructor to resolve.  Non-template constructors are
// lowered eagerly at class typecheck; an instantiated constructor
// TEMPLATE's initializers take the late path, which used to resolve a
// constructor and fail ("found no match for symbol 'leaf'"), dropping
// the body (wrong-code).
extern "C" void __CPROVER_assert(bool, const char *);
template <class _Hp> struct leaf
{
  _Hp __value_;
};
template <class... _Tp> struct impl : leaf<_Tp>...
{
  template <class... _Up> impl(_Up... __u) : leaf<_Up>{__u}...
  {
  }
};
int main()
{
  impl<char, long> d('a', 2L);
  __CPROVER_assert(
    static_cast<leaf<long> &>(d).__value_ == 2L, "pack aggregate base init");
  return 0;
}
