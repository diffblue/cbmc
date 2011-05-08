/*******************************************************************\
 
Module: Read goto object files.
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#include <xmllang/xml_parser.h>
#include <namespace.h>
#include <base_type.h>
#include <message_stream.h>

#define XML_VERSION "1.4"

#include <langapi/mode.h>

#include "read_goto_object.h"
#include "xml_goto_function_hashing.h"
#include "xml_irep_hashing.h"
#include "xml_symbol_hashing.h"

/*******************************************************************\
 
Function: read_goto_object
 
  Inputs: input stream, context, functions
 
 Outputs: true on error, false otherwise
 
 Purpose: reads a goto object xml file back into a symbol and a 
          function table
 
\*******************************************************************/

bool read_goto_object(
  std::istream &in,
  const std::string &filename,
  contextt &context,
  goto_functionst &functions,
  message_handlert &message_handler)
{ 
  message_streamt message_stream(message_handler);

  xml_parser.clear();
  xml_parser.filename = filename;
  xml_parser.in = &in;
  xml_parser.set_message_handler(message_handler);

  if (xml_parser.parse())
    return true;

  xmlt &top = xml_parser.parse_tree.element;
  
  if (top.get_attribute("version")!=XML_VERSION) 
  {
    message_stream.str <<
      "The input was compiled with a different version of "
      "goto-cc, please recompile.";
    message_stream.error();
    return true;
  }
  
  xml_irep_convertt::ireps_containert ic;
  xml_irep_convertt irepconverter(ic);
  xml_symbol_convertt symbolconverter(ic);
  xml_goto_function_convertt gfconverter(ic);
  
  if(top.name.substr(0, 11)=="goto-object")
  {    
    for(xmlt::elementst::const_iterator
        sec_it=top.elements.begin();
        sec_it != top.elements.end();
        sec_it++)
    {
      xmlt sec = *sec_it;      
      if (sec.name=="irep_hash_map") 
      {
        for(xmlt::elementst::const_iterator
            irep_it = sec.elements.begin();
            irep_it != sec.elements.end();
            irep_it++)
        {
          irept i;
          irepconverter.convert(*irep_it, i);
          irepconverter.insert(irep_it->get_attribute("id"), i);
        }
      }
      else if (sec.name=="symbols")
      {        
        for(xmlt::elementst::const_iterator
            sym_it = sec.elements.begin();
            sym_it != sec.elements.end();
            sym_it++)
        {
          symbolt symbol;
          symbolconverter.convert(*sym_it, symbol);
          // std::cout << "Adding Symbol: " << symbol.name << std::endl;
          if(!symbol.is_type &&
             symbol.type.id()=="code")
          {
            // makes sure there is an empty function
            // for this symbol. if we got code for it,
            // it will be added lateron.
            functions.function_map[symbol.name].type=
              to_code_type(symbol.type);
          }
          context.add(symbol);          
        }
      }
      else if (sec.name=="functions")
      {        
        for(xmlt::elementst::const_iterator
            fun_it = sec.elements.begin();
            fun_it != sec.elements.end();
            fun_it++)
        {
          std::string fname = fun_it->get_attribute("name");
          //std::cout << "Adding function body: " << fname << std::endl;          
          goto_functionst::goto_functiont &f = functions.function_map[fname];
          gfconverter.convert(*fun_it, f);
        }
      }
      else
      {
        message_stream.str << "Unknown Section '"
          << sec.name << "' in object file.";
        message_stream.error();
        return true;
      }

    }
  }
  else
  {
    message_stream.error("no goto-object");
    return true;
  }  
    
  xml_parser.clear();
  return false;
}
