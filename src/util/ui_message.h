/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_UI_MESSAGE_H
#define CPROVER_UTIL_UI_MESSAGE_H

#include <memory>

#include "message.h"

class json_stream_arrayt;

class ui_message_handlert:public message_handlert
{
public:
  enum class uit { PLAIN, XML_UI, JSON_UI };

  ui_message_handlert(uit, const std::string &program);
  ui_message_handlert(const class cmdlinet &, const std::string &program);
  ui_message_handlert();

  virtual ~ui_message_handlert();

  uit get_ui() const
  {
    return _ui;
  }

  void set_ui(uit __ui)
  {
    _ui=__ui;
    if(_ui == uit::JSON_UI && !json_stream)
    {
      json_stream=
        std::unique_ptr<json_stream_arrayt>(new json_stream_arrayt(out));
    }
  }

  virtual void flush(unsigned level);

  json_stream_arrayt *get_json_stream() override
  {
    return json_stream.get();
  }

protected:
  uit _ui;
  std::ostream &out;
  std::unique_ptr<json_stream_arrayt> json_stream;

  // overloading
  virtual void print(
    unsigned level,
    const std::string &message);

  // overloading
  virtual void print(
    unsigned level,
    const std::string &message,
    int sequence_number,
    const source_locationt &location);

  virtual void xml_ui_msg(
    const std::string &type,
    const std::string &msg1,
    const std::string &msg2,
    const source_locationt &location);

  virtual void json_ui_msg(
    const std::string &type,
    const std::string &msg1,
    const std::string &msg2,
    const source_locationt &location);

  virtual void ui_msg(
    const std::string &type,
    const std::string &msg1,
    const std::string &msg2,
    const source_locationt &location);

  const char *level_string(unsigned level);
};

#endif // CPROVER_UTIL_UI_MESSAGE_H
