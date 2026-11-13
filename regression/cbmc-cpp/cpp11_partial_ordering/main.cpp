// C++11 partial template specialization ordering
// When Pair<int, int> matches both <T,T> and <T,int>,
// the more specialized <T,T> should be selected.
template <typename T, typename U>
struct Pair
{
  static constexpr int id = 0;
};

template <typename T>
struct Pair<T, T>
{
  static constexpr int id = 1;
};

template <typename T>
struct Pair<T, int>
{
  static constexpr int id = 2;
};

int main()
{
  __CPROVER_assert(Pair<int, int>::id == 1, "partial ordering selects <T,T>");
  return 0;
}
