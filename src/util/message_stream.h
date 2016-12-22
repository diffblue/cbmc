/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_MESSAGE_STREAM_H
#define CPROVER_UTIL_MESSAGE_STREAM_H

#include <sstream>

#include "message.h"
#include "expr.h"

// deprecated; use warning(), error(), etc. streams in messaget

class legacy_message_streamt:public message_clientt
{
public:
  explicit legacy_message_streamt(message_handlert &_message_handler):
    message_clientt(_message_handler),
    error_found(false),
    saved_error_location(static_cast<const source_locationt &>(get_nil_irep())),
    sequence_number(1)
  {
  }

  virtual ~legacy_message_streamt() { }

  // overload to use language specific syntax
  virtual std::string to_string(const exprt &expr) { return expr.pretty(); }
  virtual std::string to_string(const typet &type) { return type.pretty(); }

  void err_location(const exprt &expr) { saved_error_location=expr.find_source_location(); }
  void err_location(const typet &type) { saved_error_location=type.source_location(); }
  void err_location(const irept &irep) { saved_error_location=static_cast<const source_locationt &>(irep.find(ID_C_source_location)); }
  void err_location(const source_locationt &_location) { saved_error_location=_location; }

  void error_msg(const std::string &message)
  {
    send_msg(1, message);
  }

  void warning_msg(const std::string &message)
  {
    send_msg(2, message);
  }

  void statistics_msg(const std::string &message)
  {
    send_msg(8, message);
  }

  void debug_msg(const std::string &message)
  {
    send_msg(9, message);
  }

  void error_msg()
  {
    send_msg(1, str.str());
    clear_err();
    sequence_number++;
  }

  void warning_msg()
  {
    send_msg(2, str.str());
    clear_err();
    sequence_number++;
  }

  void status_msg()
  {
    send_msg(6, str.str());
    clear_err();
    sequence_number++;
  }

  void statistics_msg()
  {
    send_msg(8, str.str());
    clear_err();
    sequence_number++;
  }

  void debug_msg()
  {
    send_msg(9, str.str());
    clear_err();
    sequence_number++;
  }

  std::ostringstream str;

  inline std::ostream &error()
  {
    return str;
  }

  // API stub, intentional noop
  static inline std::ostream &eom(std::ostream &m)
  {
    return m;
  }


  bool get_error_found() const
  {
    return error_found;
  }

  void error_parse(unsigned level)
  {
    error_parse(level, str.str());
    clear_err();
  }

  void clear_err()
  {
    str.clear();
    str.str("");
  }

protected:
  bool error_found;
  source_locationt saved_error_location;
  unsigned sequence_number;

  void send_msg(unsigned level, const std::string &message)
  {
    if(message=="") return;
    if(level<=1) error_found=true;

    if(message_handler!=NULL)
      message_handler->print(
        level,
        message,
        sequence_number,
        saved_error_location);

    saved_error_location.make_nil();
  }

  void error_parse_line(
    unsigned level,
    const std::string &line);

  void error_parse(
    unsigned level,
    const std::string &error);
};

#endif // CPROVER_UTIL_MESSAGE_STREAM_H
