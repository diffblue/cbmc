// Base class initializer in out-of-class template constructor
// where the base class is a nested class
struct Outer
{
  struct Inner
  {
    int x;
    Inner(int v) : x(v)
    {
    }
  };
};

template <typename T>
struct Derived : Outer::Inner
{
  Derived(int v);
};

template <typename T>
Derived<T>::Derived(int v) : Inner(v)
{
}

int main()
{
  Derived<char> d(42);
}
