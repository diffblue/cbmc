// N5008 [temp.arg.explicit]/2 + [temp.deduct.general]/2: an explicitly
// specified template argument is substituted before deduction and is
// not itself subject to it.  CBMC used to let the call-argument
// deduction overwrite the explicit binding (T re-deduced as int below
// although W was given), so get<W> got the wrong signature and became
// a bodyless stub returning nondet.  Isolated from libc++'s
// __uninitialized_allocator_move_if_noexcept<_Alloc, reverse_iterator,
// ...> (fourth layer of the vector push_back family).
extern "C" void __CPROVER_assert(bool, const char *);

struct W
{
  int v;
  W(int x) : v(x + 1)
  {
  }
};

template <class T>
int get(T a, T)
{
  return a.v;
}

int main()
{
  __CPROVER_assert(get<W>(1, 2) == 2, "explicit arg converts");
}
