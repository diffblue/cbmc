extern "C" void __CPROVER_assert(bool, const char *);
class path
{
public:
  path() : len(0)
  {
  }
  path(int n) : len(n)
  {
  }
  path &replace_extension(const path &replacement = path());
  int size() const
  {
    return len;
  }
  void set(int n = _S_default)
  {
    len = n;
  }

private:
  int len;
  static const int _S_default = 7;
};
path &path::replace_extension(const path &replacement)
{
  len = replacement.len + 10;
  return *this;
}
template <class T>
struct box
{
  T v;
  box(T init = T(3)) : v(init)
  {
  }
  void add(T d = T(1))
  {
    v = v + d;
  }
};
int main()
{
  path p(2);
  p.replace_extension();
  __CPROVER_assert(
    p.size() == 10, "default argument constructs the class being defined");
  p.set();
  __CPROVER_assert(
    p.size() == 7, "default argument names a later static member");
  box<int> b;
  b.add();
  __CPROVER_assert(
    b.v == 4, "default arguments naming the class template's parameter");
  __CPROVER_assert(b.v == 5, "WRONG (must FAIL)");
}
