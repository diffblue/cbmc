// C++23: #elifdef and #elifndef preprocessor directives
// Supported in GCC 12+, Clang 13+
#if(defined(__GNUC__) && __GNUC__ >= 12) || \
  (defined(__clang__) && __clang_major__ >= 13)

#define FOO

#ifdef BAR
int x = 1;
#elifdef FOO
int x = 2;
#else
int x = 3;
#endif

#ifdef BAR
int y = 10;
#elifndef BAZ
int y = 20;
#else
int y = 30;
#endif

int main()
{
  __CPROVER_assert(x == 2, "elifdef");
  __CPROVER_assert(y == 20, "elifndef");
}

#else

int main()
{
}

#endif
