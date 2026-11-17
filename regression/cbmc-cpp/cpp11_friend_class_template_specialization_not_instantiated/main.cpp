// N5008 [temp.inst]/2: a friend declaration does not require the befriended
// class to be complete, so naming a class template specialization in it
// does not instantiate the specialization.  libstdc++ 13's __shared_ptr
// declares `friend _Sp_atomic<shared_ptr<_Tp>>;' (C++20), and
// _Sp_atomic's members name __shared_ptr's members, declared after the
// friend declaration: <memory> with <condition_variable> was rejected.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct watcher
{
  using count_type = decltype(T::count);
  count_type seen = 0;
};
template <class T>
struct holder
{
  friend watcher<holder<T>>;
  int count = 7;
};
int main()
{
  holder<char> h;
  watcher<holder<char>> w;
  __CPROVER_assert(h.count == 7 && w.seen == 0, "friend does not instantiate");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
