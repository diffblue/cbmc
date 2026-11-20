extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;
void *operator new(size_t, void *p) noexcept
{
  return p;
}
template <class T>
struct remove_reference
{
  using type = T;
};
template <class T>
struct remove_reference<T &>
{
  using type = T;
};
template <class T>
struct remove_reference<T &&>
{
  using type = T;
};
template <class T>
constexpr T &&forward(typename remove_reference<T>::type &t) noexcept
{
  return static_cast<T &&>(t);
}
template <class T>
struct allocator
{
  template <class U, class... Args>
  void construct(U *p, Args &&...args)
  {
    ::new((void *)p) U(forward<Args>(args)...);
  }
};
struct point
{
  int x, y;
  point() : x(-1), y(-1)
  {
  }
  point(int a, int b) : x(a), y(b)
  {
  }
};
int main()
{
  allocator<int> a;
  int i = 7;
  a.construct(&i);
  __CPROVER_assert(
    i == 0, "value-initialization through an empty pack: new((void*)p) int()");
  alignas(point) unsigned char raw[sizeof(point)];
  point *p = reinterpret_cast<point *>(raw);
  allocator<point> ap;
  ap.construct(p);
  __CPROVER_assert(p->x == -1, "default constructor through an empty pack");
  ap.construct(p, 3, 4);
  __CPROVER_assert(p->x == 3 && p->y == 4, "arguments forwarded");
  __CPROVER_assert(p->y == 3, "WRONG (must FAIL)");
}
