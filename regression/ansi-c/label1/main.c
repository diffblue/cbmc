extern void foo(int *, unsigned int);

int main()
{
#ifdef _MSC_VER
label:
  int x;
#elif defined(__GNUC__)
  int *p;
  unsigned int u;
label:
  __attribute__((unused)) foo(p, u);
#endif
}
