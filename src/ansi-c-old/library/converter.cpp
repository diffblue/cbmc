#include <iostream>
#include <string>

bool has_prefix(const std::string &s, const std::string &prefix)
{
  return std::string(s, 0, prefix.size())==prefix;
}

int main()
{
  std::string line;
  bool first=true;
  
  std::cout << "{\n";

  while(getline(std::cin, line))
  {
    if(has_prefix(line, "/* FUNCTION: "))
    {
      if(first) first=false; else std::cout << "},\n";
    
      std::string function=std::string(line, 13, std::string::npos);
      std::size_t pos=function.find(' ');
      if(pos!=std::string::npos) function=std::string(function, 0, pos);

      std::cout << "{ \"c::" << function << "\",\n";
      std::cout << "  \"#line 1 \\\"<builtin-library>-" << function << "\\\"\\n\"\n";
    }
    else if(!first)
    {
      std::cout << "  \"";
      
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
  
  if(!first) std::cout << "},\n";

  std::cout << 
    "{ 0, 0 }\n"
    "};\n";
}
