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

ui_message_handlert::ui_message_handlert(
  message_handlert *message_handler,
  uit __ui,
  const std::string &program,
  bool always_flush,
  timestampert::clockt clock_type)
  : message_handler(message_handler),
    _ui(__ui),
    always_flush(always_flush),
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
      json_stream =
        std::unique_ptr<json_stream_arrayt>(new json_stream_arrayt(out));
      json_stream->push_back().make_object()["program"] = json_stringt(program);
    }
    break;
  }
}

ui_message_handlert::ui_message_handlert(
  const class cmdlinet &cmdline,
  const std::string &program)
  : ui_message_handlert(
      nullptr,
      cmdline.isset("xml-ui") ? uit::XML_UI : cmdline.isset("json-ui")
                                                ? uit::JSON_UI
                                                : uit::PLAIN,
      program,
      cmdline.isset("flush"),
      cmdline.isset("timestamp")
        ? cmdline.get_value("timestamp") == "monotonic"
            ? timestampert::clockt::MONOTONIC
            : cmdline.get_value("timestamp") == "wall"
                ? timestampert::clockt::WALL_CLOCK
                : timestampert::clockt::NONE
        : timestampert::clockt::NONE)
{
}

ui_message_handlert::ui_message_handlert(message_handlert &message_handler)
  : ui_message_handlert(
      &message_handler, uit::PLAIN, "", false, timestampert::clockt::NONE)
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
      std::stringstream ss;
      const std::string timestamp = time->stamp();
      ss << timestamp << (timestamp.empty() ? "" : " ") << message;
      if(message_handler)
      {
        message_handler->print(level, ss.str());
        if(always_flush)
          message_handler->flush(level);
      }
      else
      {
        console_message_handlert msg(always_flush);
        msg.print(level, ss.str());
        if(always_flush)
          msg.flush(level);
      }
    }
    break;

    case uit::XML_UI:
    case uit::JSON_UI:
    {
      source_locationt location;
      location.make_nil();
      print(level, message, location);
      if(always_flush)
        flush(level);
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
  const source_locationt &location)
{
  message_handlert::print(level, message);

  if(verbosity>=level)
  {
    switch(get_ui())
    {
    case uit::PLAIN:
      message_handlert::print(
        level, message, location);
      break;

    case uit::XML_UI:
    case uit::JSON_UI:
    {
      std::string tmp_message(message);

      if(!tmp_message.empty() && *tmp_message.rbegin()=='\n')
        tmp_message.resize(tmp_message.size()-1);

      const char *type=level_string(level);

      ui_msg(type, tmp_message, location);
    }
    break;
    }
  }
}

void ui_message_handlert::ui_msg(
  const std::string &type,
  const std::string &msg,
  const source_locationt &location)
{
  switch(get_ui())
  {
  case uit::PLAIN:
    break;

  case uit::XML_UI:
    xml_ui_msg(type, msg, location);
    break;

  case uit::JSON_UI:
    json_ui_msg(type, msg, location);
    break;
  }
}

void ui_message_handlert::xml_ui_msg(
  const std::string &type,
  const std::string &msg1,
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
  const source_locationt &location)
{
  INVARIANT(json_stream, "JSON stream must be initialized before use");
  json_objectt &result = json_stream->push_back().make_object();

  if(location.is_not_nil() &&
     !location.get_file().empty())
    result["sourceLocation"] = json(location);

  result["messageType"] = json_stringt(type);
  result["messageText"] = json_stringt(msg1);
  const std::string timestamp = time->stamp();
  if(!timestamp.empty())
    result["timestamp"] = json_stringt(timestamp);
}

void ui_message_handlert::flush(unsigned level)
{
  switch(get_ui())
  {
  case uit::PLAIN:
  {
    if(message_handler)
    {
      message_handler->flush(level);
    }
    else
    {
      console_message_handlert msg(always_flush);
      msg.flush(level);
    }
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
