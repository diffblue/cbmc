/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_COUT_MESSAGE_H

#define CPROVER_COUT_MESSAGE_H

#include <iostream>
#include <message.h>

class cout_message_handlert:public message_handlert
{
public:
  virtual void print(unsigned level, const std::string &message)
  { std::cout << message << std::endl; }
};
 
class cerr_message_handlert:public message_handlert
{
public:
  virtual void print(unsigned level, const std::string &message)
  { std::cerr << message << std::endl; }
};
 
class console_message_handlert:public message_handlert
{
public:
  virtual void print(unsigned level, const std::string &message)
  { 
    if(level>1)
      std::cout << message << std::endl;
    else
      std::cerr << message << std::endl;
  }
};
 
#endif
