// C++26 language features require GCC 12+
#if !defined(__GNUC__) && !defined(_MSC_VER) || __GNUC__ >= 12
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

#else
int main()
{
}
#endif
