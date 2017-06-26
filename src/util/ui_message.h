/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_UI_MESSAGE_H
#define CPROVER_UTIL_UI_MESSAGE_H

#include "message.h"

class ui_message_handlert:public message_handlert
{
public:
  enum class uit { PLAIN, XML_UI, JSON_UI };

  ui_message_handlert(uit, const std::string &program);
  ui_message_handlert(const class cmdlinet &, const std::string &program);
  ui_message_handlert():
    _ui(uit::PLAIN)
  {
  }

  virtual ~ui_message_handlert();

  uit get_ui() const
  {
    return _ui;
  }

  void set_ui(uit __ui)
  {
    _ui=__ui;
  }

  virtual void flush(unsigned level);

protected:
  uit _ui;

  // overloading
  virtual void print(
    unsigned level,
    const std::string &message,
    bool preformatted);

  // overloading
  virtual void print(
    unsigned level,
    const std::string &message,
    int sequence_number,
    const source_locationt &location,
    bool preformatted);

  virtual void xml_ui_msg(
    const std::string &type,
    const std::string &msg1,
    const std::string &msg2,
    const source_locationt &location,
    bool preformatted);

  virtual void json_ui_msg(
    const std::string &type,
    const std::string &msg1,
    const std::string &msg2,
    const source_locationt &location,
    bool preformatted);

  virtual void ui_msg(
    const std::string &type,
    const std::string &msg1,
    const std::string &msg2,
    const source_locationt &location,
    bool preformatted);

  const char *level_string(unsigned level);
};

#endif // CPROVER_UTIL_UI_MESSAGE_H
