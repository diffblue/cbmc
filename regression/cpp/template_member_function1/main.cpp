// Template member function called from within the class body
namespace ns
{
struct tag
{
};
} // namespace ns

struct S
{
  template <typename T>
  void construct(T a, T b, ns::tag)
  {
  }

  void init(const char *p)
  {
    construct(p, p + 5, ns::tag());
  }
};

int main()
{
  S s;
  s.init("hello");
}
