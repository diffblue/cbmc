// Template argument deduction should not match when a deduced parameter
// type is a class but the actual argument is arithmetic/enum.
template <typename T>
struct W
{
  T val;
  W(T v) : val(v)
  {
  }
};

template <typename T>
W<T> operator-(const W<T> &a, const T &b)
{
  return W<T>(a.val - b);
}

int main()
{
  enum
  {
    N = 6
  };
  int x = N - 1; // must use built-in operator-, not W::operator-
  return x;
}
