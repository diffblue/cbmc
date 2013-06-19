#include <iostream>

#include "osx_fat_reader.h"

int main(int argc, char **argv)
{
  if(argc!=2)
  {
    std::cerr << "osx_fat_reader_test universal_binary_file" << std::endl;
    return 1;
  }

  try
  {
    std::ifstream in(argv[1]);
    osx_fat_readert osx_fat_reader(in);

    bool sect=osx_fat_reader.has_gb();

    std::cout << "hppa7100LC architecture present? " << sect << std::endl;
  }

  catch(const char *s)
  {
    std::cerr << "Exception: " << s << std::endl;
  }

  return 0;
}
