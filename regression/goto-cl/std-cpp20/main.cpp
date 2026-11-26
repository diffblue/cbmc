// /std:c++20 selects C++20: consteval and requires-expressions
consteval int square(int x)
{
  return x * x;
}

template <class T>
constexpr bool has_size = requires(T t) { t.size(); };

struct sized
{
  int size() const
  {
    return 1;
  }
};

int main()
{
  static_assert(square(3) == 9, "consteval");
  static_assert(has_size<sized> && !has_size<int>, "requires-expression");
  return 0;
}
