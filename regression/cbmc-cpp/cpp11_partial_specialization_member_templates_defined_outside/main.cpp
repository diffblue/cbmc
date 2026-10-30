extern "C" void __CPROVER_assert(bool, const char *);
template <class>
class function;
template <class R, class... A>
class function<R(A...)>
{
public:
  int which;
  template <class F, class = F>
  function(F);
  template <class F, class G, class H>
  function(F, G, H);
};
// N5008 [temp.mem]/1, [temp.over.link]/6-7: each out-of-class definition
// defines the member template whose template-head and signature it repeats
template <class R, class... A>
template <class F, class>
function<R(A...)>::function(F) : which(1)
{
}
template <class R, class... A>
template <class F, class G, class H>
function<R(A...)>::function(F, G, H) : which(3)
{
}
int main()
{
  function<int()> f(0);
  function<int()> g(0, 0, 0);
  __CPROVER_assert(f.which == 1, "one-parameter constructor template");
  __CPROVER_assert(g.which == 3, "three-parameter constructor template");
  __CPROVER_assert(f.which == 3, "WRONG (must FAIL)");
  return 0;
}
