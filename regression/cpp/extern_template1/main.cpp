// Extern template declaration for a member function template
template <typename T>
struct S
{
  template <typename U>
  T convert(U v);
};

template <typename T>
template <typename U>
T S<T>::convert(U v)
{
  return static_cast<T>(v);
}

extern template int S<int>::convert(double);

int main()
{
  S<int> s;
}
