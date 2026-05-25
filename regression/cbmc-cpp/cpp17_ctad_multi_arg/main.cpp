// C++17: CTAD with multi-argument constructors
template <typename T>
struct Pair
{
  T first;
  T second;
  Pair(T a, T b) : first(a), second(b)
  {
  }
};

template <typename T, typename U>
struct Mixed
{
  T a;
  U b;
  Mixed(T x, U y) : a(x), b(y)
  {
  }
};

int main()
{
  Pair p(1, 2);
  __CPROVER_assert(p.first + p.second == 3, "same type CTAD");

  Mixed m(1, 3.0);
  __CPROVER_assert(m.a == 1, "mixed type CTAD");
}
