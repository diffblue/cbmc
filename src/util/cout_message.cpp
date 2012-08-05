/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "cout_message.h"

void cout_message_handlert::print(
  unsigned level,
  const std::string &message)
{
  std::cout << message << std::endl;
}
 
void cerr_message_handlert::print(
  unsigned level,
  const std::string &message)
{
  std::cerr << message << std::endl;
}
 
void console_message_handlert::print(
  unsigned level,
  const std::string &message)
{ 
  if(level>1)
    std::cout << message << std::endl;
  else
    std::cerr << message << std::endl;
}
