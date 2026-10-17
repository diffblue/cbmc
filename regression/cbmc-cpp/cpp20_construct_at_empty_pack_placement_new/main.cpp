extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;
void *operator new(size_t, void *p) noexcept
{
  return p;
}
// libc++ <__memory/construct_at.h>: the constraint is a placement-new inside
// decltype whose new-initializer expands the parameter pack; the pack is not
// the last template parameter ([temp.param]/14)
namespace std
{
template <class T>
T &&declval() noexcept;
template <class T>
T *addressof(T &r) noexcept
{
  return __builtin_addressof(r);
}
template <class T>
void *__voidify(T &loc) noexcept
{
  return const_cast<void *>(static_cast<const volatile void *>(addressof(loc)));
}
template <
  class T,
  class... Args,
  class = decltype(::new(std::declval<void *>()) T(std::declval<Args>()...))>
constexpr T *construct_at(T *loc, Args &&...args)
{
  return ::new(std::__voidify(*loc)) T(static_cast<Args &&>(args)...);
}
} // namespace std
struct point
{
  int x, y;
  point(int a, int b) : x(a), y(b)
  {
  }
};
int main()
{
  char buf[4] = {'a', 'b', 'c', 'd'};
  std::construct_at(std::addressof(buf[1]));
  __CPROVER_assert(
    buf[0] == 'a',
    "value-initialization of a char is allowed by the default argument");
  alignas(point) unsigned char raw[sizeof(point)];
  point *p = std::construct_at(reinterpret_cast<point *>(raw), 3, 4);
  __CPROVER_assert(p->x == 3 && p->y == 4, "constructor arguments forwarded");
  __CPROVER_assert(p->x == 4, "WRONG (must FAIL)");
}
