#ifdef same_return_type
#  define T int
#else
#  define T struct b
#endif

int a()
{
  T a(c);
}

int main()
{
}
