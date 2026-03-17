// C++17 optional-like with std::optional pattern
template <typename T>
struct Optional
{
  bool has_val;
  T val;
  Optional() : has_val(false), val()
  {
  }
  Optional(T v) : has_val(true), val(v)
  {
  }
  bool has_value() const
  {
    return has_val;
  }
  T value() const
  {
    return val;
  }
};
int main()
{
  Optional<int> a;
  Optional<int> b(42);
  __CPROVER_assert(!a.has_value(), "empty");
  __CPROVER_assert(b.has_value(), "has value");
  __CPROVER_assert(b.value() == 42, "value is 42");
  return 0;
}
