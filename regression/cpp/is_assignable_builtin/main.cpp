struct S
{
  int x;
};

// __is_assignable(T&, U) should be true when U is convertible to T
// and T is non-const.
static_assert(__is_assignable(int &, int), "");
static_assert(__is_assignable(int &, const int &), "");
static_assert(__is_assignable(S &, const S &), "");

int main()
{
}
