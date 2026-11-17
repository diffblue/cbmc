// C++23 language features require GCC 11+
#if !defined(__GNUC__) && !defined(_MSC_VER) || __GNUC__ >= 11
// C++23: #warning preprocessor directive
#  warning "This is a test warning"

int main()
{
  __CPROVER_assert(1, "ok");
}

#else
int main()
{
}
#endif
