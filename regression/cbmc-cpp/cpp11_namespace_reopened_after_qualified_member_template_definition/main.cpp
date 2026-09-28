extern "C" void __CPROVER_assert(bool, const char *);
namespace fmt
{
struct sink
{
  int n = 3;
};
template <class>
using str_sink = sink;
template <class, class...>
class arg_store;
} // namespace fmt
// [namespace.memdef]/2: a member of a namespace may be defined outside it
// by a qualified name
template <class, class...>
class fmt::arg_store
{
};
namespace fmt
{
} // namespace fmt
int use()
{
  fmt::str_sink<char> buf;
  return buf.n;
}
int main()
{
  __CPROVER_assert(use() == 3, "fmt:: names the namespace");
  __CPROVER_assert(use() == 4, "WRONG (must FAIL)");
}
