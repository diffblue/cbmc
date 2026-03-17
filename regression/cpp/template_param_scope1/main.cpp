struct MyAlloc
{
  typedef int value_type;
};

template <typename A>
struct Traits
{
  typedef typename A::value_type vt;
};

int main()
{
  Traits<MyAlloc>::vt x = 42;
  return 0;
}
