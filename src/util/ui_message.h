/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UI_LANGUAGE_H
#define CPROVER_UI_LANGUAGE_H

#include <message.h>

class ui_message_handlert:public message_handlert
{
public:
  typedef enum { PLAIN, XML_UI } uit;
  
  ui_message_handlert(uit __ui, const std::string &program);   
  virtual ~ui_message_handlert();

  uit get_ui() const
  {
    return _ui;
  }

protected:
  uit _ui;
 
  // overloading
  virtual void print(
    unsigned level,
    const std::string &message);

  // overloading
  virtual void print(
    unsigned level,
    const std::string &message,
    int sequence_number,
    const locationt &location);

  virtual void old_gui_msg(
    const std::string &type,
    const std::string &msg1,
    const std::string &msg2,
    const locationt &location);

  virtual void xml_ui_msg(
    const std::string &type,
    const std::string &msg1,
    const std::string &msg2,
    const locationt &location);

  virtual void ui_msg(
    const std::string &type,
    const std::string &msg1,
    const std::string &msg2,
    const locationt &location);

  const char *level_string(unsigned level);
};

#endif
