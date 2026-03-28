#if __has_include(<coroutine>)
// C++20 <coroutine> header parses
#  include <coroutine>
int main()
{
  std::__n4861::coroutine_handle<void> h;
  __CPROVER_assert(h.address() == nullptr, "null handle");
}

#else
int main()
{
}
#endif
