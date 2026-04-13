// valarray internals changed in GCC 16, causing pointer arithmetic failures
#if !defined(__GNUC__) && !defined(_MSC_VER) || __GNUC__ <= 15
#  include <cassert>
#  include <valarray>
int main()
{
  std::valarray<int> v(3);
  v[0] = 1;
  v[1] = 2;
  v[2] = 3;
  assert(v.sum() == 6);
  return 0;
}

#else
int main()
{
}
#endif
