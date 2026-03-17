// Template member function with two overloads and tag dispatch
namespace ns
{
struct input_tag
{
};
struct forward_tag : input_tag
{
};
} // namespace ns

template <typename CharT>
struct basic_string
{
  basic_string()
  {
  }

  template <typename InIter>
  void construct(InIter beg, InIter end, ns::input_tag)
  {
  }

  template <typename FwdIter>
  void construct(FwdIter beg, FwdIter end, ns::forward_tag)
  {
  }

  template <typename Iter>
  basic_string(Iter beg, Iter end)
  {
    construct(beg, end, ns::forward_tag());
  }
};

int main()
{
  const char *p = "hello";
  basic_string<char> s(p, p + 5);
}
