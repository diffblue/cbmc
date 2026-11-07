// Out-of-class member definitions for templates in inline namespaces
// should be found through the using-scope.
namespace outer
{
inline namespace inner
{
template <typename T>
class Base
{
public:
  void method();
  T value;
};
} // namespace inner

template <typename T>
void Base<T>::method()
{
  value = T();
}
} // namespace outer

int main()
{
  outer::Base<int> b;
  b.method();
  return 0;
}
