extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [intro.object]/9: a base subobject of empty class type has zero
// size; it may share its address with the derived object's other
// subobjects, and initializing it stores nothing
struct ph
{
};
struct leaf0
{
  int *value;
  leaf0(int *v) : value(v)
  {
  }
};
struct copied : private ph
{
  copied(const ph &p) : ph(p)
  {
  }
};
struct forwarded : private ph
{
  template <class T>
  forwarded(T &&p) : ph(static_cast<T &&>(p))
  {
  }
};
struct value_initialized : private ph
{
  value_initialized() : ph()
  {
  }
};
struct t1 : leaf0, copied
{
  t1(int *v, const ::ph &p) : leaf0(v), copied(p)
  {
  }
};
struct t2 : leaf0, forwarded
{
  t2(int *v, ::ph &p) : leaf0(v), forwarded(p)
  {
  }
};
struct t3 : leaf0, value_initialized
{
  t3(int *v) : leaf0(v)
  {
  }
};
int main()
{
  int a[2] = {7, 8};
  ph p;
  t1 x1(&a[1], p);
  t2 x2(&a[1], p);
  t3 x3(&a[1]);
  __CPROVER_assert(x1.value == &a[1], "copy-initialized empty base");
  __CPROVER_assert(x2.value == &a[1], "constructor template");
  __CPROVER_assert(x3.value == &a[1], "value-initialized empty base");
  __CPROVER_assert(*x1.value == 7, "WRONG (must FAIL)");
  return 0;
}
