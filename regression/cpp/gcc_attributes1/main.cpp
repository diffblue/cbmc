#ifdef __GNUC__
const char *__attribute__((weak)) bar();
#endif

int main()
{
#ifdef __GNUC__
  return bar() != 0;
#else
  return 0
#endif
}
