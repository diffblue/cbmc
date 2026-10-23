extern "C" void __CPROVER_assert(bool, const char *);
typedef decltype(sizeof(0)) size_t;
void *operator new(size_t, void *p) noexcept
{
  return p;
}
struct base
{
  virtual int call() = 0;
  virtual void destroy(bool) noexcept = 0;
};
template <class F>
struct impl : base
{
  F f;
  impl(F g) : f(g)
  {
  }
  int call() override
  {
    return f();
  }
  void destroy(bool) noexcept override
  {
    this->~impl();
  }
};
// N5008 [basic.life]/1, [expr.new]: the MSVC STL std::function constructs
// its target by placement new at the start of a union whose last pointer
// element points to it; a virtual call through that pointer reaches the
// target ([class.virtual]/2)
constexpr int num_ptrs = 6 + 16 / sizeof(void *);
struct function
{
  union storage
  {
    char space[(num_ptrs - 1) * sizeof(void *)];
    base *ptrs[num_ptrs];
  } st;
  base *get() const
  {
    return st.ptrs[num_ptrs - 1];
  }
  void set(base *p)
  {
    st.ptrs[num_ptrs - 1] = p;
  }
  template <class F>
  function(F f)
  {
    set(::new(static_cast<void *>(&st)) impl<F>(f));
  }
  ~function()
  {
    if(get())
    {
      get()->destroy(get() != static_cast<const void *>(&st));
      set(nullptr);
    }
  }
  int operator()() const
  {
    return get()->call();
  }
};
int two()
{
  return 2;
}
int main()
{
  function b = two;
  __CPROVER_assert(b() == 2, "call");
  __CPROVER_assert(b() == 3, "WRONG (must FAIL)");
  return 0;
}
