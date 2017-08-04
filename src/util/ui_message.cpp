/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ui_message.h"

#include <fstream>
#include <iostream>

#include "xml.h"
#include "json.h"
#include "xml_expr.h"
#include "cout_message.h"
#include "cmdline.h"

ui_message_handlert::ui_message_handlert(
  uit __ui, const std::string &program):_ui(__ui)
{
  switch(__ui)
  {
  case uit::PLAIN:
    break;

  case uit::XML_UI:
    std::cout << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" << "\n";
    std::cout << "<cprover>" << "\n";

    {
      xmlt program_xml;
      program_xml.name="program";
      program_xml.data=program;

      std::cout << program_xml;
    }
    break;

  case uit::JSON_UI:
    {
      std::cout << "[\n";
      json_objectt json_program;
      json_program["program"] = json_stringt(program);
      std::cout << json_program;
    }
    break;
  }
}

ui_message_handlert::ui_message_handlert(
  const class cmdlinet &cmdline,
  const std::string &program):
  ui_message_handlert(
    cmdline.isset("xml-ui")?uit::XML_UI:
    cmdline.isset("json-ui")?uit::JSON_UI:
    uit::PLAIN,
    program)
{
}

ui_message_handlert::~ui_message_handlert()
{
  switch(get_ui())
  {
  case uit::XML_UI:
    std::cout << "</cprover>" << "\n";
    break;

  case uit::JSON_UI:
    std::cout << "\n]\n";
    break;

  case uit::PLAIN:
    break;
  }
}

const char *ui_message_handlert::level_string(unsigned level)
{
  if(level==1)
    return "ERROR";
  else if(level==2)
    return "WARNING";
  else
    return "STATUS-MESSAGE";
}

void ui_message_handlert::print(
  unsigned level,
  const std::string &message,
  bool preformatted)
{
  if(verbosity>=level)
  {
    switch(get_ui())
    {
    case uit::PLAIN:
    {
      console_message_handlert console_message_handler;
      console_message_handler.print(level, message, preformatted);
    }
    break;

    case uit::XML_UI:
    case uit::JSON_UI:
    {
      source_locationt location;
      location.make_nil();
      print(level, message, -1, location, preformatted);
    }
    break;
    }
  }
}

void ui_message_handlert::print(
  unsigned level,
  const std::string &message,
  int sequence_number,
  const source_locationt &location,
  bool preformatted)
{
  message_handlert::print(level, message, preformatted);

  if(verbosity>=level)
  {
    switch(get_ui())
    {
    case uit::PLAIN:
      message_handlert::print(
        level, message, sequence_number, location, preformatted);
      break;

    case uit::XML_UI:
    case uit::JSON_UI:
    {
      std::string tmp_message(message);

      if(!tmp_message.empty() && *tmp_message.rbegin()=='\n')
        tmp_message.resize(tmp_message.size()-1);

      const char *type=level_string(level);

      std::string sequence_number_str=
        sequence_number>=0?std::to_string(sequence_number):"";

      ui_msg(type, tmp_message, sequence_number_str, location, preformatted);
    }
    break;
    }
  }
}

void ui_message_handlert::ui_msg(
  const std::string &type,
  const std::string &msg1,
  const std::string &msg2,
  const source_locationt &location,
  bool preformatted)
{
  switch(get_ui())
  {
  case uit::PLAIN:
    break;

  case uit::XML_UI:
    xml_ui_msg(type, msg1, msg2, location, preformatted);
    break;

  case uit::JSON_UI:
    json_ui_msg(type, msg1, msg2, location, preformatted);
    break;
  }
}

void ui_message_handlert::xml_ui_msg(
  const std::string &type,
  const std::string &msg1,
  const std::string &msg2,
  const source_locationt &location,
  bool preformatted)
{
  if(preformatted)
  {
    // Expect the message is already an XML fragment.
    std::cout << msg1 << '\n';
    return;
  }

  xmlt result;
  result.name="message";

  if(location.is_not_nil() &&
     !location.get_file().empty())
    result.new_element(xml(location));

  result.new_element("text").data=msg1;
  result.set_attribute("type", type);

  std::cout << result;
  std::cout << '\n';
}

void ui_message_handlert::json_ui_msg(
  const std::string &type,
  const std::string &msg1,
  const std::string &msg2,
  const source_locationt &location,
  bool preformatted)
{
  if(preformatted)
  {
    // Expect the message is already a JSON fragment.
    std::cout << ",\n" << msg1;
    return;
  }

  json_objectt result;

  #if 0
  if(location.is_not_nil() &&
     !location.get_file().empty())
    result.new_element(xml(location));
  #endif

  result["messageType"] = json_stringt(type);
  result["messageText"] = json_stringt(msg1);

  // By convention a leading comma is created by every new array entry.
  // The first entry is generated in the constructor and does not have
  //  a trailing comma.
  std::cout << ",\n" << result;
}

void ui_message_handlert::flush(unsigned level)
{
  switch(get_ui())
  {
  case uit::PLAIN:
  {
    console_message_handlert console_message_handler;
    console_message_handler.flush(level);
  }
  break;

  case uit::XML_UI:
  case uit::JSON_UI:
  {
    std::cout << std::flush;
  }
  break;
  }
}
