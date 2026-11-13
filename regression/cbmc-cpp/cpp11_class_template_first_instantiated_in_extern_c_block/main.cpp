// N5008 [temp.pre]/6, [dcl.link]/5: a template has C++ language linkage,
// and so have its specializations, wherever they are instantiated.  Here
// the class template is first instantiated for the member of a struct
// declared in an extern "C" block.  The out-of-line definitions of its
// member functions were converted with C linkage: as functions of their own
// name without `this', so that `set' did not resolve uniquely and the two
// overloads of `assign' collided ("already declared with different type").
extern "C" void __CPROVER_assert(bool, const char *);
template <typename T, T v>
struct tag
{
};
typedef tag<bool, true> true_tag;
typedef tag<bool, false> false_tag;
template <typename T>
struct box
{
  T v;
  void set(T x);
  void assign(box &x, true_tag);
  void assign(box &x, false_tag);
};
template <typename T>
void box<T>::set(T x)
{
  v = x;
}
template <typename T>
void box<T>::assign(box &x, true_tag)
{
  v = x.v;
}
template <typename T>
void box<T>::assign(box &x, false_tag)
{
  v = x.v + 1;
}
extern "C"
{
  struct holder
  {
    box<int> b;
  };
}
int main()
{
  holder h, g;
  h.b.set(3);
  __CPROVER_assert(h.b.v == 3, "member function");
  g.b.set(5);
  h.b.assign(g.b, true_tag{});
  __CPROVER_assert(h.b.v == 5, "overload");
  h.b.assign(g.b, false_tag{});
  __CPROVER_assert(h.b.v == 6, "other overload");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
