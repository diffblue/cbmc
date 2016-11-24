// Debian package fcoe-utils
#ifdef __GNUC__
int* foo(int *) __asm__("" "my_real_name");
#endif

int main()
{
  #ifdef __GNUC__
  int x;
  return foo(&x)==&x ? 0 : 42;
  #else
  return 0;
  #endif
}
