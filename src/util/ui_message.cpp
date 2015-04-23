/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <iostream>

#include "i2string.h"
#include "xml.h"
#include "xml_expr.h"
#include "cout_message.h"
#include "ui_message.h"

/*******************************************************************\

Function: ui_message_handlert::ui_message_handlert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ui_message_handlert::ui_message_handlert(
  uit __ui, const std::string &program):_ui(__ui)
{
  switch(__ui)
  {
  case XML_UI:
    std::cout << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" << "\n";
    std::cout << "<cprover>" << "\n";
    
    {
      xmlt program_xml;
      program_xml.name="program";
      program_xml.data=program;
      
      std::cout << program_xml;
    }
    break;
    
  case PLAIN:
    break;
    
  default:;
  }
}

/*******************************************************************\

Function: ui_message_handlert::~ui_message_handlert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ui_message_handlert::~ui_message_handlert()
{
  if(get_ui()==XML_UI)
    std::cout << "</cprover>" << "\n";
}

/*******************************************************************\

Function: ui_message_handlert::level_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const char *ui_message_handlert::level_string(unsigned level)
{
  if(level==1)
    return "ERROR";
  else if(level==2)
    return "WARNING";
  else
    return "STATUS-MESSAGE";
}

/*******************************************************************\

Function: ui_message_handlert::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ui_message_handlert::print(
  unsigned level,
  const std::string &message)
{
  if(verbosity>=level)
  {
    if(get_ui()==XML_UI)
    {
      source_locationt location;
      location.make_nil();
      print(level, message, -1, location);
    }
    else
    {
      console_message_handlert console_message_handler;
      console_message_handler.print(level, message);
    }
  }
}

/*******************************************************************\

Function: ui_message_handlert::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ui_message_handlert::print(
  unsigned level,
  const std::string &message,
  int sequence_number,
  const source_locationt &location)
{
  if(verbosity>=level)
  {
    if(get_ui()==XML_UI)
    {
      std::string tmp_message(message);

      if(!tmp_message.empty() && *tmp_message.rbegin()=='\n')
        tmp_message.resize(tmp_message.size()-1);
    
      const char *type=level_string(level);
      
      std::string sequence_number_str=
        sequence_number>=0?i2string(sequence_number):"";

      ui_msg(type, tmp_message, sequence_number_str, location);
    }
    else
    {
      message_handlert::print(
        level, message, sequence_number, location);
    }
  }
}

/*******************************************************************\

Function: ui_message_handlert::ui_msg

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ui_message_handlert::ui_msg(
  const std::string &type,
  const std::string &msg1,
  const std::string &msg2,
  const source_locationt &location)
{
  xml_ui_msg(type, msg1, msg2, location);
}

/*******************************************************************\

Function: ui_message_handlert::xml_ui_msg

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ui_message_handlert::xml_ui_msg(
  const std::string &type,
  const std::string &msg1,
  const std::string &msg2,
  const source_locationt &location)
{
  xmlt result;
  result.name="message";

  if(location.is_not_nil() && location.get_file()!="")
    result.new_element(xml(location));

  result.new_element("text").data=msg1;
  result.set_attribute("type", type);
  
  std::cout << result;
  std::cout << std::endl;
}

