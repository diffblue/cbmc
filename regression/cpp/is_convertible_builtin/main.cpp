static_assert(__is_convertible(int, long), "int -> long");
static_assert(__is_convertible(int, double), "int -> double");
static_assert(!__is_convertible(int *, int), "int* -> int");
static_assert(__is_convertible(int *, const int *), "int* -> const int*");
static_assert(__is_convertible(void, void), "void -> void");
static_assert(!__is_convertible(void, int), "void -> int");
static_assert(!__is_convertible(int, void), "int -> void");

int main()
{
  return 0;
}
