#include <iostream>
#include <string>

int main()
{
  std::string line;

  while(getline(std::cin, line))
  {
    std::cout << "\"";
    
    for(unsigned i=0; i<line.size(); i++)
    {
      const char ch=line[i];
      if(ch=='\\')
        std::cout << "\\\\";
      else if(ch=='"')
        std::cout << "\\\"";
      else if(ch=='\r' || ch=='\n')
      {
      }
      else
        std::cout << ch;
    }
    
    std::cout << "\\n\"" << std::endl;
  }
}
