// Template converting constructors should work for implicit conversions
// and direct construction.

struct error_code
{
  error_code() : val(0)
  {
  }
  template <typename E>
  error_code(E e) : val(static_cast<int>(e))
  {
  }
  int val;
};

enum class io_errc
{
  stream = 1
};

void foo(const error_code &ec = io_errc::stream)
{
}

int main()
{
  error_code ec1(io_errc::stream);
  error_code ec2 = io_errc::stream;
  foo();
  return 0;
}
