template <typename T>
struct S
{
  typedef T type;
};

template <typename T>
struct S<const T>
{
  typedef const T type;
};

int main()
{
  S<int>::type x = 1;
  S<const int>::type y = 2;
  return 0;
}
