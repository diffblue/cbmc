extern "C" void __CPROVER_assert(bool, const char *);
struct handle
{
  int x = 7;
};
// libc++'s std::mutex shape: a defaulted default constructor, a default
// member initializer, a user-declared destructor
struct mutex_like
{
  handle h = {};
  mutex_like() = default;
  mutex_like(const mutex_like &) = delete;
  ~mutex_like() noexcept;
};
mutex_like::~mutex_like() noexcept
{
}
struct throwing
{
  throwing() noexcept(false);
};
// [except.spec]/8: an implicitly-declared or defaulted default constructor is
// noexcept unless an immediate subexpression of a default member initializer
// or a subobject's default constructor is potentially-throwing
static_assert(__is_nothrow_constructible(mutex_like), "defaulted, nothrow");
static_assert(__is_nothrow_constructible(handle), "implicit, nothrow");
static_assert(!__is_nothrow_constructible(throwing), "potentially-throwing");
int main()
{
  bool b = __is_nothrow_constructible(mutex_like);
  __CPROVER_assert(b, "nothrow default construction");
  __CPROVER_assert(!b, "WRONG (must FAIL)");
}
