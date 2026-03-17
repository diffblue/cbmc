// C++11 move semantics
struct S
{
  int *data;
  S() : data(new int(42))
  {
  }
  S(S &&other) : data(other.data)
  {
    other.data = nullptr;
  }
  ~S()
  {
    delete data;
  }
};
int main()
{
  S a;
  S b(static_cast<S &&>(a));
  __CPROVER_assert(b.data != nullptr, "moved data");
  __CPROVER_assert(a.data == nullptr, "source nulled");
  return 0;
}
