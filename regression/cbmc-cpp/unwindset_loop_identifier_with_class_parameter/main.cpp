// The identifier of a loop in a function whose parameter has class type
// contains a comma and parentheses,
// `ns::fill(ptr_signed_int,struct_tag(identifier=ns::tag-it)).0', and
// --unwindset splits its argument at every comma.
extern "C" void __CPROVER_assert(bool, const char *);

namespace ns
{
struct it
{
  int *p;
};
void fill(int *p, it)
{
  for(int i = 0; i < 3; ++i)
    p[i] = 2;
}
} // namespace ns

int main()
{
  int a[3];
  ns::it o = {a};
  ns::fill(a, o);
  __CPROVER_assert(a[2] == 2, "filled");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
