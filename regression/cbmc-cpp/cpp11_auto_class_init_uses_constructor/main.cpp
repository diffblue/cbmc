// N5008 [dcl.init]/16.6.2 + [class.copy.elision]: `auto x = init;' of a
// class type is copy-initialization -- the copy or move constructor chosen
// by overload resolution (a prvalue initializes the object directly), not a
// bitwise copy.  The front end assigned bitwise and then destroyed the
// source temporary: `auto g = make();' (libstdc++ 16's `auto __guard =
// std::__allocate_guarded_obj(__alloc)' in std::list::_M_create_node) freed
// the resource the new object still referenced, `auto b = a;' let both
// destructors release a's resource.
extern "C" void __CPROVER_assert(bool, const char *);
int live = 0;
struct res
{
  int *p;
  res(int v) : p(new int(v))
  {
    ++live;
  }
  res(const res &o) : p(new int(*o.p))
  {
    ++live;
  }
  res(res &&o) : p(o.p)
  {
    o.p = nullptr;
  }
  ~res()
  {
    if(p)
    {
      --live;
      delete p;
    }
  }
};
res make()
{
  return res(7);
}
int main()
{
  {
    auto g = make(); // prvalue: no copy, one live object
    __CPROVER_assert(g.p != nullptr && *g.p == 7, "owns the result");
    __CPROVER_assert(live == 1, "exactly one live object");
    res a(1);
    auto b = a; // copy constructor
    __CPROVER_assert(live == 3 && b.p != a.p && *b.p == 1, "copy constructed");
    auto c = static_cast<res &&>(a); // move constructor
    __CPROVER_assert(
      live == 3 && a.p == nullptr && *c.p == 1, "move constructed");
  }
  __CPROVER_assert(live == 0, "every resource released exactly once");
  return 0;
}
