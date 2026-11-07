// C++17 class template argument deduction with aggregate
template <typename T, typename U>
struct Pair
{
  T first;
  U second;
};
// Deduction guide
template <typename T, typename U>
Pair(T, U) -> Pair<T, U>;
int main()
{
  Pair p{1, 2.0};
  __CPROVER_assert(p.first == 1, "first");
  return 0;
}
