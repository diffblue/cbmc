// C++11 constexpr member function call on constexpr variable
struct S
{
  int x;
  constexpr int get() const
  {
    return x;
  }
};

int main()
{
  constexpr S s{42};
  __CPROVER_assert(s.get() == 42, "constexpr member call");
  return 0;
}
