// C++11 template method defined outside class
struct Container
{
  int val;
  template <typename U>
  U convert() const;
};

template <typename U>
U Container::convert() const
{
  return static_cast<U>(val);
}

int main()
{
  Container c{42};
  double r = c.convert<double>();
  __CPROVER_assert(r > 41.0, "template method outside class");
  return 0;
}
