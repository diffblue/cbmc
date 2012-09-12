/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_COUT_MESSAGE_H

#define CPROVER_COUT_MESSAGE_H

#include <message.h>

class cout_message_handlert:public message_handlert
{
public:
  // all messages go to cout
  virtual void print(unsigned level, const std::string &message);
};
 
class cerr_message_handlert:public message_handlert
{
public:
  // all messages go to cerr
  virtual void print(unsigned level, const std::string &message);
};
 
class console_message_handlert:public message_handlert
{
public:
  // level 4 and upwards go to cout, level 1-3 to cerr
  virtual void print(unsigned level, const std::string &message);
};
 
#endif
