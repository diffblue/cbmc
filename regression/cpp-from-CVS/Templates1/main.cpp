template <typename T>
void f(T x)
{
  assert(x);
}

template <int i>
void eq(int z)
{
  assert(i==z);
}

int main()
{
  eq<2>(2);
  f<int>(1);
}
