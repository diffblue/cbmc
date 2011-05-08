/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ERROR_HANDLER_H
#define CPROVER_ERROR_HANDLER_H

#include <sstream>

#include "message.h"
#include "expr.h"

class message_streamt:public message_clientt
{
public:
  message_streamt(message_handlert &_message_handler):
    message_clientt(_message_handler),
    error_found(false),
    saved_error_location(static_cast<const locationt &>(get_nil_irep())),
    sequence_number(1)
  {
  }

  virtual ~message_streamt() { }

  // overload to use language specific syntax
  virtual std::string to_string(const exprt &expr) { return expr.to_string(); }
  virtual std::string to_string(const typet &type) { return type.to_string(); }

  void err_location(const exprt &expr) { saved_error_location=expr.find_location(); }
  void err_location(const typet &type) { saved_error_location=type.location(); }
  void err_location(const irept &irep) { saved_error_location=(const locationt &)irep.find("#location"); }
  void err_location(const locationt &_location) { saved_error_location=_location; }

  void error(const std::string &message)
  {
    send_msg(1, message);
  }

  void warning(const std::string &message)
  {
    send_msg(2, message);
  }

  void statistics(const std::string &message)
  {
    send_msg(8, message);
  }
  
  void debug(const std::string &message)
  {
    send_msg(9, message);
  }
  
  void error()
  {
    send_msg(1, str.str());
    clear_err();
    sequence_number++;
  }

  void warning()
  {
    send_msg(2, str.str());
    clear_err();
    sequence_number++;
  }
  
  void status()
  {
    send_msg(6, str.str());
    clear_err();
    sequence_number++;
  }
  
  void statistics()
  {
    send_msg(8, str.str());
    clear_err();
    sequence_number++;
  }
  
  std::ostringstream str;
  
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
  locationt saved_error_location;
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

#endif
