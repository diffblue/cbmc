#include <iostream>

#include <util/cout_message.h>

#include <json/json_parser.h>

int yyjsonlex();
extern char *yyjsontext;

int main()
{
  #if 0
  int token;
  while((token=yyjsonlex())!=0)
  {
    std::cout << "token: " << token << "\n";
    std::cout << "yyjsontext: " << yyjsontext << "\n";
  }
  #endif

  bool result;

  console_message_handlert message_handler;

  jsont json;

  result=parse_json(std::cin, "", message_handler, json);

  std::cout << "return value: " << result << "\n\n";
  std::cout << json << "\n";
}
