template <typename T>
class Wrapper
{
  T val;

public:
  template <typename... Args>
  Wrapper(Args &&...args) : val{static_cast<Args &&>(args)...}
  {
  }
  T get() const
  {
    return val;
  }
};

int main()
{
  Wrapper<int> w(42);
  __CPROVER_assert(w.get() == 42, "value is 42");
  return 0;
}
