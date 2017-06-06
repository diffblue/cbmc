/*******************************************************************\

Module: Convert file contents to C strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Convert file contents to C strings

#include <iostream>
#include <string>

int main()
{
  std::string line;

  while(getline(std::cin, line))
  {
    std::cout << "\"";

    for(std::size_t i=0; i<line.size(); i++)
    {
      const char ch=line[i];
      if(ch=='\\')
        std::cout << "\\\\";
      else if(ch=='"')
        std::cout << "\\\"";
      else if(ch=='\r' || ch=='\n')
      {
      }
      else if((ch&0x80)!=0)
      {
        std::cout << "\\x"
                  << std::hex << (unsigned(ch)&0xff)
                  << std::dec;
      }
      else
        std::cout << ch;
    }

    std::cout << "\\n\"\n";
  }
}
