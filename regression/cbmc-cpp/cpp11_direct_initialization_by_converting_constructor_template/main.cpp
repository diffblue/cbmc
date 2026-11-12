// N5008 [dcl.init.general]/16.6.2.1, [over.match.ctor]: `W w(a);' is
// direct-initialization; the constructors of W are candidates, and the
// constructor template W(X) with X = alloc is an exact match for the
// const alloc lvalue.  Before C++17 the front end converted a to a W
// temporary by that constructor and copy-constructed w from it.  With a
// base whose copy constructor is deleted (libstdc++'s
// _Sp_counted_ptr_inplace(_Alloc, _Args &&...) from _Sp_counted_base), the
// copy constructor's body was dropped and w was nondeterministic
// (std::make_shared in <condition_variable>).
extern "C" void __CPROVER_assert(bool, const char *);
struct alloc
{
};
struct base
{
  base() = default;
  base(const base &) = delete;
};
struct W : base
{
  int via;
  template <class X>
  W(X) : via(1)
  {
  }
};
template <class A>
struct inplace final : base
{
  int via;
  template <class... Args>
  inplace(A, Args &&...) : via(sizeof...(Args) + 1)
  {
  }
};
int main()
{
  const alloc a{};
  W w(a);
  __CPROVER_assert(w.via == 1, "constructor template");
  inplace<alloc> *p = new inplace<alloc>(a);
  __CPROVER_assert(p->via == 1, "variadic constructor template");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
