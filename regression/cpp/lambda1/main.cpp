// C++11: lambda expressions in template code
template <typename F>
void call(F f)
{
  f();
}

template <typename T>
void test(T x)
{
  call([] { return 0; });
  call([x] { return x; });
  call([&x] { return x; });
  call([=] { return x; });
  call([&] { return x; });
  call([](int a) -> int { return a; });
}

int main()
{
  return 0;
}
