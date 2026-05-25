struct S
{
  int val;
};

template <typename T>
struct W
{
  T val;
  void f(const W &other)
  {
    auto &m = const_cast<W &>(other);
    m.val = T();
  }
};

int main()
{
  S s;
  auto m = s;

  W<int> w;
  w.f(w);

  return 0;
}
