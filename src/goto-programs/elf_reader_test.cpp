#include <iostream>
#include <fstream>

#include "elf_reader.h"

int main(int argc, char **argv)
{
  if(argc!=2)
  {
    std::cerr << "elf_reader_test elf_file" << std::endl;
    return 1;
  }

  std::ifstream in(argv[1]);

  try
  {
    elf_readert elf_reader(in);
  
    // iterate over sections
    for(unsigned i=0; i<elf_reader.section_header_table.size(); i++)
    {
      std::cout << "S" << i << ": " << elf_reader.section_name(i) << std::endl;
    }  
  }
  
  catch(const char *s)
  {
    std::cerr << "Exception: " << s << std::endl;
  }
  
  return 0;
}
