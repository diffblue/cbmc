#if !defined(_MSC_VER) && __has_include(<coroutine>)
// C++20 <coroutine> header parses
#  include <coroutine>
int main()
{
  std::coroutine_handle<void> h;
  __CPROVER_assert(h.address() == nullptr, "null handle");
}

#else
int main()
{
}
#endif
