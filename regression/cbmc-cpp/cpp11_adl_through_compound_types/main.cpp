extern "C" void __CPROVER_assert(bool, const char *);
namespace lib
{
struct item
{
  int value;
};
struct opaque;
int get(const item *i)
{
  return i->value;
}
int count(opaque *)
{
  return 7;
}
int first(item (*a)[2])
{
  return (*a)[0].value;
}
int apply(int (*f)(item))
{
  item i{5};
  return f(i);
}
int member(int item::*m)
{
  item i{6};
  return i.*m;
}
} // namespace lib
namespace client
{
int twice(lib::item i)
{
  return 2 * i.value;
}
int use(const lib::item *i, lib::opaque *o)
{
  lib::item pair[2] = {{3}, {4}};
  // [basic.lookup.argdep]/3: the associated namespaces of a pointer, an array
  // and a function type are those of the types they are made of, also of an
  // incomplete class
  return get(i) + count(o) + first(&pair) + apply(twice) +
         member(&lib::item::value);
}
} // namespace client
int main()
{
  lib::item i{1};
  __CPROVER_assert(client::use(&i, nullptr) == 1 + 7 + 3 + 10 + 6, "found");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
