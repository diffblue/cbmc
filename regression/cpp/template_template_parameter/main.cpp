// Test template template parameters.
template <class T>
struct MyVec
{
  T val;
};

template <template <class> class Container, class T>
struct Wrapper
{
  Container<T> data;
};

int main()
{
  Wrapper<MyVec, int> w;
  w.data.val = 42;
}
