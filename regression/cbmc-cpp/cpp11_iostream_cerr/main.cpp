#if defined(__GNUC__) && __GNUC__ >= 13
#  include <iostream>

int main(int argc, char *argv[])
{
  std::cerr << "Test" << std::endl;
  return 0;
}
#else
int main()
{
}
#endif
