// C++23: #elifdef and #elifndef preprocessor directives
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
