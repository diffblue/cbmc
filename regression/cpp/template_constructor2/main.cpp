// Template constructor in template class with copy constructor
template <typename CharT>
struct basic_string
{
  basic_string()
  {
  }
  basic_string(const basic_string &other)
  {
  }
  template <typename InputIterator>
  basic_string(InputIterator beg, InputIterator end)
  {
  }
};

template <typename String, typename CharT>
String to_xstring(CharT *buf, CharT *end)
{
  return String(buf, end);
}

void test_copy()
{
  basic_string<char> s1;
  basic_string<char> s2(s1);
}

void test_template_ctor()
{
  char buf[10];
  basic_string<char> s = to_xstring<basic_string<char>, char>(buf, buf + 10);
}

int main()
{
  test_copy();
  test_template_ctor();
}
