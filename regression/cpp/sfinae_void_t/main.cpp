// Test SFINAE with __void_t pattern: partial specialization that accesses
// a member of a non-class type should be silently skipped.

template <typename...>
using __void_t = void;

template <typename T, typename = __void_t<>>
struct has_type
{
  static const int value = 0;
};

template <typename T>
struct has_type<T, __void_t<typename T::type>>
{
  static const int value = 1;
};

struct WithType
{
  typedef int type;
};

int main()
{
  // int has no ::type, so the partial specialization should be skipped
  int a = has_type<int>::value;
  // WithType has ::type, so the partial specialization should match
  int b = has_type<WithType>::value;
  return a + b;
}
