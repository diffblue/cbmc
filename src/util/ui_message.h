/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_UI_MESSAGE_H
#define CPROVER_UTIL_UI_MESSAGE_H

#include <memory>

#include "message.h"
#include "timestamper.h"

class console_message_handlert;
class json_stream_arrayt;

class ui_message_handlert : public message_handlert
{
public:
  enum class uit { PLAIN, XML_UI, JSON_UI };

  ui_message_handlert(const class cmdlinet &, const std::string &program);

  explicit ui_message_handlert(message_handlert &);
  ui_message_handlert(ui_message_handlert &&) = default;

  virtual ~ui_message_handlert();

  virtual uit get_ui() const
  {
    return _ui;
  }

  virtual void flush(unsigned level) override;

  virtual json_stream_arrayt &get_json_stream()
  {
    PRECONDITION(json_stream!=nullptr);
    return *json_stream;
  }
  void print(unsigned level, const structured_datat &data) override;

protected:
  std::unique_ptr<console_message_handlert> console_message_handler;
  message_handlert *message_handler;
  uit _ui;
  const bool always_flush;
  std::unique_ptr<const timestampert> time;
  std::ostream &out;
  std::unique_ptr<json_stream_arrayt> json_stream;

  ui_message_handlert(
    message_handlert *,
    uit,
    const std::string &program,
    const bool always_flush,
    timestampert::clockt clock_type);

  virtual void print(
    unsigned level,
    const std::string &message) override;

  virtual void print(
    unsigned level,
    const std::string &message,
    const source_locationt &location) override;

  virtual void print(
    unsigned level,
    const xmlt &data) override;

  virtual void print(
    unsigned level,
    const jsont &data) override;

  virtual void xml_ui_msg(
    const std::string &type,
    const std::string &msg,
    const source_locationt &location);

  virtual void json_ui_msg(
    const std::string &type,
    const std::string &msg,
    const source_locationt &location);

  virtual void ui_msg(
    const std::string &type,
    const std::string &msg,
    const source_locationt &location);

  const char *level_string(unsigned level);

  std::string command(unsigned c) const override
  {
    if(!message_handler)
      return std::string();

    switch(_ui)
    {
    case uit::PLAIN:
      switch(c)
      {
      case '<': // fall through
      case '>':
        return "'";
      }
      break;
    case uit::XML_UI:
      switch(c)
      {
      case 0:  // reset
      case 1:  // bold
      case 2:  // faint
      case 3:  // italic
      case 4:  // underline
      case 31: // red
      case 32: // green
      case 33: // yellow
      case 34: // blue
      case 35: // magenta
      case 36: // cyan
      case 91: // bright_red
      case 92: // bright_green
      case 93: // bright_yellow
      case 94: // bright_blue
      case 95: // bright_magenta
      case 96: // bright_cyan
        return std::string();
      case '<': // quote_begin
        return "<quote>";
      case '>': // quote_end
        return "</quote>";
      }
      break;
    case uit::JSON_UI:
      switch(c)
      {
      case 0:  // reset
      case 1:  // bold
      case 2:  // faint
      case 3:  // italic
      case 4:  // underline
      case 31: // red
      case 32: // green
      case 33: // yellow
      case 34: // blue
      case 35: // magenta
      case 36: // cyan
      case 91: // bright_red
      case 92: // bright_green
      case 93: // bright_yellow
      case 94: // bright_blue
      case 95: // bright_magenta
      case 96: // bright_cyan
        return std::string();
      case '<': // quote_begin
      case '>': // quote_end
        return "'";
      }
      break;
    }

    return message_handler->command(c);
  }
};

#define OPT_FLUSH "(flush)"

#define HELP_FLUSH " --flush                      flush every line of output\n"

#endif // CPROVER_UTIL_UI_MESSAGE_H
