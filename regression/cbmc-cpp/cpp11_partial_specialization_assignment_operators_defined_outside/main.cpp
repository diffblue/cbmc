extern "C" void __CPROVER_assert(bool, const char *);
typedef decltype(nullptr) nullptr_t;
template <class>
class function;
template <class R, class... A>
class function<R(A...)>
{
public:
  int which = 0;
  function() = default;
  function &operator=(const function &);
  function &operator=(function &&);
  function &operator=(nullptr_t);
  template <class F, class = int>
  function &operator=(F &&);
};
// N5008 [temp.local]/1: in these out-of-class definitions of members of a
// partial specialization, `function' without template arguments is the
// injected-class-name and denotes function<R(A...)> itself; each
// definition belongs to the member with its signature ([temp.over.link])
template <class R, class... A>
function<R(A...)> &function<R(A...)>::operator=(const function &)
{
  which = 1;
  return *this;
}
template <class R, class... A>
function<R(A...)> &function<R(A...)>::operator=(function &&)
{
  which = 2;
  return *this;
}
template <class R, class... A>
function<R(A...)> &function<R(A...)>::operator=(nullptr_t)
{
  which = 3;
  return *this;
}
template <class R, class... A>
template <class F, class>
function<R(A...)> &function<R(A...)>::operator=(F &&)
{
  which = 4;
  return *this;
}
int main()
{
  function<int(const int &)> f;
  f = [](const int &x) { return x; };
  __CPROVER_assert(f.which == 4, "assignment from a lambda");
  f = nullptr;
  __CPROVER_assert(f.which == 3, "assignment from nullptr");
  function<int(const int &)> g;
  const function<int(const int &)> &cf = f;
  g = cf;
  __CPROVER_assert(g.which == 1, "copy assignment");
  g = static_cast<function<int(const int &)> &&>(f);
  __CPROVER_assert(g.which == 2, "move assignment");
  __CPROVER_assert(f.which == 4, "WRONG (must FAIL)");
  return 0;
}
