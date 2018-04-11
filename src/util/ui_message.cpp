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
#include "json_expr.h"
#include "json_stream.h"
#include "cout_message.h"
#include "cmdline.h"

ui_message_handlert::ui_message_handlert()
  : _ui(uit::PLAIN),
    time(timestampert::make(timestampert::clockt::NONE)),
    out(std::cout),
    json_stream(nullptr)
{
}

ui_message_handlert::ui_message_handlert(
  uit __ui,
  const std::string &program,
  timestampert::clockt clock_type)
  : _ui(__ui),
    time(timestampert::make(clock_type)),
    out(std::cout),
    json_stream(nullptr)
{
  switch(_ui)
  {
  case uit::PLAIN:
    break;

  case uit::XML_UI:
    out << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
        << "\n";
    out << "<cprover>"
        << "\n";

    {
      xmlt program_xml;
      program_xml.name="program";
      program_xml.data=program;

      out << program_xml;
    }
    break;

  case uit::JSON_UI:
    {
      if(!json_stream)
      {
        json_stream =
          std::unique_ptr<json_stream_arrayt>(new json_stream_arrayt(out));
      }

      INVARIANT(json_stream, "JSON stream must be initialized before use");
      json_stream->push_back().make_object()["program"] = json_stringt(program);
    }
    break;
  }
}

ui_message_handlert::ui_message_handlert(
  const class cmdlinet &cmdline,
  const std::string &program)
  : ui_message_handlert(
      cmdline.isset("xml-ui") ? uit::XML_UI : cmdline.isset("json-ui")
                                                ? uit::JSON_UI
                                                : uit::PLAIN,
      program,
      cmdline.isset("timestamp")
        ? cmdline.get_value("timestamp") == "monotonic"
            ? timestampert::clockt::MONOTONIC
            : cmdline.get_value("timestamp") == "wall"
                ? timestampert::clockt::WALL_CLOCK
                : timestampert::clockt::NONE
        : timestampert::clockt::NONE)
{
}

ui_message_handlert::~ui_message_handlert()
{
  switch(get_ui())
  {
  case uit::XML_UI:

    out << "</cprover>"
        << "\n";
    break;

  case uit::JSON_UI:
    INVARIANT(json_stream, "JSON stream must be initialized before use");
    json_stream->close();
    out << '\n';
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
  const std::string &message)
{
  if(verbosity>=level)
  {
    switch(get_ui())
    {
    case uit::PLAIN:
    {
      console_message_handlert console_message_handler;
      std::stringstream ss;
      const std::string timestamp = time->stamp();
      ss << timestamp << (timestamp.empty() ? "" : " ") << message;
      console_message_handler.print(level, ss.str());
    }
    break;

    case uit::XML_UI:
    case uit::JSON_UI:
    {
      source_locationt location;
      location.make_nil();
      print(level, message, -1, location);
    }
    break;
    }
  }
}

void ui_message_handlert::print(
  unsigned level,
  const xmlt &data)
{
  if(verbosity>=level)
  {
    switch(get_ui())
    {
    case uit::PLAIN:
      INVARIANT(false, "Cannot print xml data on PLAIN UI");
      break;
    case uit::XML_UI:
      out << data << '\n';
      flush(level);
      break;
    case uit::JSON_UI:
      INVARIANT(false, "Cannot print xml data on JSON UI");
      break;
    }
  }
}

void ui_message_handlert::print(
  unsigned level,
  const jsont &data)
{
  if(verbosity>=level)
  {
    switch(get_ui())
    {
    case uit::PLAIN:
      INVARIANT(false, "Cannot print json data on PLAIN UI");
      break;
    case uit::XML_UI:
      INVARIANT(false, "Cannot print json data on XML UI");
      break;
    case uit::JSON_UI:
      INVARIANT(json_stream, "JSON stream must be initialized before use");
      json_stream->push_back(data);
      flush(level);
      break;
    }
  }
}

void ui_message_handlert::print(
  unsigned level,
  const std::string &message,
  int sequence_number,
  const source_locationt &location)
{
  message_handlert::print(level, message);

  if(verbosity>=level)
  {
    switch(get_ui())
    {
    case uit::PLAIN:
      message_handlert::print(
        level, message, sequence_number, location);
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

      ui_msg(type, tmp_message, sequence_number_str, location);
    }
    break;
    }
  }
}

void ui_message_handlert::ui_msg(
  const std::string &type,
  const std::string &msg1,
  const std::string &msg2,
  const source_locationt &location)
{
  switch(get_ui())
  {
  case uit::PLAIN:
    break;

  case uit::XML_UI:
    xml_ui_msg(type, msg1, msg2, location);
    break;

  case uit::JSON_UI:
    json_ui_msg(type, msg1, msg2, location);
    break;
  }
}

void ui_message_handlert::xml_ui_msg(
  const std::string &type,
  const std::string &msg1,
  const std::string &msg2,
  const source_locationt &location)
{
  xmlt result;
  result.name="message";

  if(location.is_not_nil() &&
     !location.get_file().empty())
    result.new_element(xml(location));

  result.new_element("text").data=msg1;
  result.set_attribute("type", type);
  const std::string timestamp = time->stamp();
  if(!timestamp.empty())
    result.set_attribute("timestamp", timestamp);

  out << result;
  out << '\n';
}

void ui_message_handlert::json_ui_msg(
  const std::string &type,
  const std::string &msg1,
  const std::string &msg2,
  const source_locationt &location)
{
  INVARIANT(json_stream, "JSON stream must be initialized before use");
  json_objectt &result = json_stream->push_back().make_object();

  if(location.is_not_nil() &&
     !location.get_file().empty())
    result["sourceLocation"] = json_exprt()(location);

  result["messageType"] = json_stringt(type);
  result["messageText"] = json_stringt(msg1);
  const std::string timestamp = time->stamp();
  if(!timestamp.empty())
    result["timestamp"] = json_stringt(timestamp);

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
    out << std::flush;
  }
  break;
  }
}
