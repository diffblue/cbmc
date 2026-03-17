// Forward declaration with unnamed parameter
template <typename>
class Alloc;

// Definition with named parameter
template <typename _Tp>
class Alloc
{
public:
  typedef _Tp value_type;
  _Tp *allocate(int n)
  {
    return 0;
  }
};

template <typename T>
struct Container
{
  typedef Alloc<T> allocator_type;
  allocator_type a;
};

int main()
{
  Container<int> c;
  return 0;
}
