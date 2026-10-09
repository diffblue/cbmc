// Non-type template arguments containing '<' must not confuse the parser
// into treating '<' as the start of nested template arguments.
template <bool>
struct integral_constant
{
};

template <int _Size>
struct bitset
{
  void f()
  {
    integral_constant < bool, _Size<8>();
    integral_constant < bool, _Size<8> x;
    integral_constant<bool, (_Size < 8)>();
    integral_constant < bool, _Size<sizeof(int)>();
  }
};

int main()
{
  return 0;
}
