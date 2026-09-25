// C++20: class type NTTP with brace initialization
struct Fixed
{
  int value;
  constexpr Fixed(int v) : value(v)
  {
  }
};
template <Fixed F>
int get()
{
  return F.value;
}
int main()
{
  int r = get<Fixed{42}>();
  __CPROVER_assert(r == 42, "class NTTP brace");
}
