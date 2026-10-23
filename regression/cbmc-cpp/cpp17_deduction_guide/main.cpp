// C++17 deduction guides
template <typename T>
struct Wrapper
{
  T val;
  Wrapper(T v) : val(v)
  {
  }
};

template <typename T>
Wrapper(T) -> Wrapper<T>;

int main()
{
  Wrapper w(42);
  __CPROVER_assert(w.val == 42, "deduction guide");
  return 0;
}
