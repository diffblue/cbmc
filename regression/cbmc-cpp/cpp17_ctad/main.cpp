// C++17 class template argument deduction
template <typename T>
struct Wrapper
{
  T value;
  Wrapper(T v) : value(v)
  {
  }
};

int main()
{
  Wrapper w(42);
  __CPROVER_assert(w.value == 42, "CTAD");
  return 0;
}
