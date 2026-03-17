// Test C++11 forwarding references (T&&) and reference collapsing.

template <typename T>
struct remove_reference
{
  typedef T type;
};

template <typename T>
struct remove_reference<T &>
{
  typedef T type;
};

template <typename T>
struct remove_reference<T &&>
{
  typedef T type;
};

template <typename T>
typename remove_reference<T>::type &&my_move(T &&t)
{
  return static_cast<typename remove_reference<T>::type &&>(t);
}

struct A
{
  int x;
};

int main()
{
  A a;
  a.x = 42;
  A b = my_move(a);
  A c = my_move(A());
}
