// Partial explicit template arguments for function templates
template <typename To, typename From>
To my_cast(From x)
{
  return static_cast<To>(x);
}

template <typename To, typename From1, typename From2>
To combine(From1 a, From2 b)
{
  return static_cast<To>(a) + static_cast<To>(b);
}

int main()
{
  double d = 3.14;
  int i = my_cast<int>(d);
  long l = combine<long>(1, 2.0);
  return 0;
}
