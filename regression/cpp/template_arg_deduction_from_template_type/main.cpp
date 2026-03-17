// Test template argument deduction where template parameters appear
// as arguments to another template type in the function parameter list.
// This pattern is used by std::chrono::duration_cast.

template <typename Rep, typename Period>
struct duration
{
  Rep r;
};

typedef duration<long, int> seconds;

template <typename _ToDur, typename _Rep, typename _Period>
_ToDur duration_cast(const duration<_Rep, _Period> &__d)
{
  return _ToDur();
}

long test(const duration<long, int> &d)
{
  seconds s = duration_cast<seconds>(d);
  return s.r;
}

int main()
{
  duration<long, int> d;
  d.r = 42;
  test(d);
  return 0;
}
