template <typename T>
struct Base
{
  T val;
};

template <typename T>
using Alias = Base<T>;

Alias<int> a;
Alias<double> b;

int main()
{
  a.val = 1;
  b.val = 2.0;
  return 0;
}
