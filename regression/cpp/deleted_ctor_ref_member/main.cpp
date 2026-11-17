// Deleted constructors should not trigger member initialization.
// A class with a reference member and a deleted copy constructor
// should not cause "reference must be explicitly initialized" errors.
struct S
{
  S(int &r) : ref(r)
  {
  }
  S(const S &) = delete;
  int &ref;
};

int main()
{
  int x = 0;
  S s(x);
  return 0;
}
