// N5008 [class.member.lookup] / [basic.scope.hiding]: a member declared in a
// class hides an inherited member of the same name.  In a recursively-derived
// class template -- `TImpl<I, Head, Tail...> : HeadBase<I, Head>,
// TImpl<I+1, Tail...>` -- every level redefines `typedef HeadBase<I, Head>
// _Base;`, so the inherited `TImpl<I+1,...>::_Base` is hidden by this level's
// own `_Base`.  An unqualified `_Base` inside `TImpl<0,int,double>::M_head`
// must therefore denote `HeadBase<0,int>`, not the inherited
// `TImpl<1,double>::_Base` (= `HeadBase<1,double>`).
//
// This is the shape of libstdc++'s std::tuple `_M_head`
// (`_Tuple_impl<_Idx,_Head,_Tail...>::_M_head` delegates to `_Base::_M_head`
// where `_Base` is `_Head_base<_Idx,_Head>`).  Regression: the qualified-name
// resolver picked the *inherited* same-named member typedef, so
// `TImpl<0,int,double>::M_head`'s body resolved `_Base::M_head` to
// `HeadBase<1,double>::M_head` (a `double&` returner); the int& body then
// failed to type-check and was dropped, leaving the call returning a nondet
// value.  Fixed in filter_for_named_scopes (cpp_typecheck_resolve.cpp) by
// preferring the class's own member typedef over an inherited one.
//
// Called from a non-main function body so the member function is type-checked
// during the deferred method-body drain (the failing context).
//
// Assertion 1 SUCCEEDs (the head element is read); assertion 2 (a wrong value)
// FAILs, proving the assertions are evaluated non-vacuously.

template <unsigned long I, typename H>
struct HeadBase
{
  H h;
  static H &M_head(HeadBase &b)
  {
    return b.h;
  }
};

template <unsigned long, typename...>
struct TImpl;

template <unsigned long I>
struct TImpl<I>
{
};

template <unsigned long I, typename Head, typename... Tail>
struct TImpl<I, Head, Tail...> : HeadBase<I, Head>, TImpl<I + 1, Tail...>
{
  typedef HeadBase<I, Head> _Base;
  static Head &M_head(TImpl &t)
  {
    return _Base::M_head(t);
  }
};

int wrapper(TImpl<0, int, double> &t)
{
  return TImpl<0, int, double>::M_head(t);
}

int main()
{
  TImpl<0, int, double> t;
  static_cast<HeadBase<0, int> &>(t).h = 7;
  int n = wrapper(t);
  __CPROVER_assert(n == 7, "own member typedef hides inherited one");
  __CPROVER_assert(n == 99, "WRONG (must FAIL)");
  return 0;
}
