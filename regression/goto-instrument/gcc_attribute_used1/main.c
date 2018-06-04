#ifdef __GNUC__
static int foo __attribute__((used)) = 42;
#else
int foo = 42;
#endif

int main()
{
  return 0;
}
