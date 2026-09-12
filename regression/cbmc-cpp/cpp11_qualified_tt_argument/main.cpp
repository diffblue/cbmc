extern "C" void __CPROVER_assert(bool, const char *);
namespace outer
{
template <class T>
struct box
{
  T v;
};
} // namespace outer
template <template <class> class TT>
struct user
{
  TT<int> b;
};
int main()
{
  // N5008 [temp.arg.template]/1: a template-argument for a template
  // template-parameter is a template-name, which may be QUALIFIED
  // (id-expression naming outer::box).
  user<outer::box> u;
  u.b.v = 7;
  __CPROVER_assert(u.b.v == 7, "qualified template-name as TT-argument");
  return 0;
}
