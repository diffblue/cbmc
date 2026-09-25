template <typename>
class B;

template <typename T>
class A
{
  void secret()
  {
  }
  template <typename>
  friend class B;
};

template <typename T>
class B
{
public:
  void test(A<T> &a)
  {
    a.secret();
  }

  class Inner
  {
    void nested_test(A<T> &a)
    {
      a.secret();
    }
  };
};

int main()
{
  B<int> b;
  A<int> a;
  b.test(a);
  return 0;
}
