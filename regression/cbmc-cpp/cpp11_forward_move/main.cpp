namespace std
{
template <typename _Tp>
struct remove_reference
{
  typedef _Tp type;
};
template <typename _Tp>
struct remove_reference<_Tp &>
{
  typedef _Tp type;
};
template <typename _Tp>
struct remove_reference<_Tp &&>
{
  typedef _Tp type;
};

template <typename _Tp>
_Tp &&forward(typename remove_reference<_Tp>::type &__t) noexcept
{
  return static_cast<_Tp &&>(__t);
}

template <typename _Tp>
_Tp &&forward(typename remove_reference<_Tp>::type &&__t) noexcept
{
  return static_cast<_Tp &&>(__t);
}

template <typename _Tp>
typename remove_reference<_Tp>::type &&move(_Tp &&__t) noexcept
{
  return static_cast<typename remove_reference<_Tp>::type &&>(__t);
}
} // namespace std

// Named rvalue reference is an lvalue — forward should select lvalue overload
void test_forward(int &&x)
{
  int &&y = std::forward<int>(x);
}

// Named rvalue reference is an lvalue — move should deduce _Tp as int&
void test_move(int &&x)
{
  int &&y = std::move(x);
}

int main()
{
  test_forward(42);
  test_move(42);
  return 0;
}
