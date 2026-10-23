// C++11 exception specifications and ref-qualifiers
struct S
{
  void f() noexcept;
  void g() noexcept(true);
  void h() throw();
  int value() const &noexcept;
  int value() &&noexcept;
};

void S::f() noexcept
{
}
void S::g() noexcept(true)
{
}
void S::h() throw()
{
}

int main()
{
  S s;
  s.f();
  return 0;
}
