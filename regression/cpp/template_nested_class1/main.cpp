// Out-of-class nested class definition for a template class
template <typename T>
class Outer
{
public:
  class Inner;
  T value;
};

template <typename T>
class Outer<T>::Inner
{
  int x;
};

int main()
{
  Outer<int> o;
  o.value = 42;
}
