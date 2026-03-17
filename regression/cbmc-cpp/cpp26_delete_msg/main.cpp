// C++26 = delete("message")
struct S
{
  S() = delete("use factory function instead");
};

S make_s();

int main()
{
  return 0;
}
