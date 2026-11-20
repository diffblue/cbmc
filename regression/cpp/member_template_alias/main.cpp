struct Base1
{
  int x;
};
struct Base2
{
  int y;
};

struct Wrapper
{
  template <typename T>
  using type = T;
};

// Member template alias used as a type
typedef Wrapper::type<Base1> result_type;

// Member template alias used as a base class
template <bool>
struct selector
{
  template <typename T, typename>
  using type = T;
};

template <>
struct selector<false>
{
  template <typename, typename U>
  using type = U;
};

template <bool B, typename T, typename F>
using select_t = typename selector<B>::template type<T, F>;

struct Derived : select_t<true, Base1, Base2>
{
  int z;
};

int main()
{
  result_type r;
  r.x = 1;

  Derived d;
  d.x = 2;
  d.z = 3;
}
