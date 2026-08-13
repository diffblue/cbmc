// N5008 [dcl.init.list]/3.2 + [dcl.init.general]/16.6.1: a single
// initializer of the base's own type (a synthesized copy constructor's
// sliced-reference initializer, or a by-value slicing static_cast) is
// COPY-initialization of the base subobject, not element-wise aggregate
// initialization.  The [class.base.init]/7 aggregate lowering must not
// intercept it: doing so tried to convert the whole base value to the
// base's FIRST member ("invalid implicit conversion from 'const struct
// leaf' to 'struct box'", a hard error that killed the whole TU).
extern "C" void __CPROVER_assert(bool, const char *);
struct box
{
  int v;
  box(int x) : v(x)
  {
  }
};
template <class T> struct leaf
{
  T value_;
  T get()
  {
    return value_;
  }
};
struct impl : leaf<box>
{
};
int take(impl c)
{
  return static_cast<leaf<box>>(c).get().v;
}
int main()
{
  impl d{box(7)};
  __CPROVER_assert(take(d) == 7, "impl by value");
  return 0;
}
