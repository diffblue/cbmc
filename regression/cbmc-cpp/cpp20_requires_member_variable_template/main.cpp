extern "C" void __CPROVER_assert(bool, const char *);
template <typename _Tp>
struct optional
{
  template <typename, typename = _Tp>
  static constexpr bool ok = true;
  int val = 0;
  optional()
  {
  }
  template <typename _Up = _Tp>
  requires ok<_Up> optional(_Up v) : val(v)
  {
  }
};
int main()
{
  optional<int> o = 42;
  __CPROVER_assert(o.val == 42, "requires over variable template");
  return 0;
}
