extern "C" void __CPROVER_assert(bool, const char *);
#include <typeinfo>
struct Plain
{
  int x;
};
struct WithMemberTemplate
{
  int x;
  template <class T>
  void set(T &&v)
  {
    x = static_cast<int>(v);
  }
  template <class... Ts>
  int count(Ts &&...) const
  {
    return sizeof...(Ts);
  }
};
template <class T>
const std::type_info &info()
{
  return typeid(T);
}
int main()
{
  __CPROVER_assert(
    typeid(Plain) == typeid(Plain), "typeid of plain class is stable");
  __CPROVER_assert(
    typeid(WithMemberTemplate) == info<WithMemberTemplate>(),
    "typeid of a class with member templates");
  __CPROVER_assert(
    typeid(WithMemberTemplate) != typeid(Plain),
    "distinct classes have distinct type_info");
  WithMemberTemplate w;
  w.set(3);
  __CPROVER_assert(
    w.x == 3 && w.count(1, 2) == 2, "member templates still usable");
  return 0;
}
