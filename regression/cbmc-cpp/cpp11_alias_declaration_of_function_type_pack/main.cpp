extern "C" void __CPROVER_assert(bool, const char *);
int hit;
void cb(int k, char)
{
  hit = k;
}
// [dcl.typedef]/2, [temp.variadic]/5: F is void(int, char) for X<int, char>
template <class... T>
struct X
{
  using F = void(T...);
  F *p;
};
int main()
{
  X<int, char> x;
  x.p = cb;
  x.p(3, 'c');
  __CPROVER_assert(hit == 3, "alias of a function type with a pack");
  __CPROVER_assert(hit != 3, "WRONG (must FAIL)");
}
