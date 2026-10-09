template <typename T>
struct A
{
};

template <typename R, typename... Args>
struct A<R(Args...)>
{
  typedef R result_type;
};

int main()
{
  A<bool(char)>::result_type r;
}
