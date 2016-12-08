class T
{
public:
  T()
  {
  }

  typedef int my_type;

  void f()
  {
    T::my_type x;
    ::T::my_type y;
    my_type z;
  }
};

int main()
{
}
