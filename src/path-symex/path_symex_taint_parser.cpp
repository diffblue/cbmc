/*******************************************************************
 Module: Taint Parser

 Author: Daniel Neville,	daniel.neville@cs.ox.ac.uk
 John Galea,		john.galea@cs.ox.ac.uk

 \*******************************************************************/

#include "path_symex_taint_parser.h"

/*******************************************************************
 Function: parse_taint_file

 Inputs:  Takes file name of JSON and taint engine.
 Stores parsed rules in taint_data.

 Outputs: Returns true on parsing errors

 Purpose: Parses JSON file and stores rules

 \*******************************************************************/
bool parse_taint_file(const std::string &file_name,
    message_handlert &message_handler, taint_datat &taint_data,
    taint_enginet &taint_engine)
{
  /* Format of JSON File.
   Array of Objects.
   Each Object:
   loc: <Program location s.t. LHS is tainted>
   taint: <Taint value>
   symbol: <expanded symbol> (Optional)
   */

  jsont json;

  // First parse the file.
  if(parse_json(file_name, message_handler, json))
  {
    messaget message(message_handler);
    message.error() << "Taint file is not a valid json file" << messaget::eom;
    return true;
  }

  // Perform array check.
  if(!json.is_array())
  {
    messaget message(message_handler);
    message.error() << "expecting an array in the input location file, but got "
        << json << messaget::eom;
    return true;
  }

  for (jsont::arrayt::const_iterator it=json.array.begin();
      it != json.array.end(); it++)
  {
    if(!it->is_object())
    {
      messaget message(message_handler);
      message.error()
          << "expecting an array of objects in the input location file, but got "
          << *it << messaget::eom;
      return true;
    }

    const std::string taint_string=(*it)["taint"].value;
    const std::string loc_string=(*it)["loc"].value;
    const std::string symbol_string=(*it)["symbol"].value;

    taintt taint=0;
    unsigned int loc=0;
    irep_idt symbol_name="";
    bool symbol_flag=false;

    try
    {
      // TODO: Handle catch better.
      taint=taint_engine.parse_taint(taint_string);
    } catch (...)
    {
      messaget message(message_handler);
      message.error() << "Taint type not recognised." << messaget::eom;
    }

    if(loc_string.empty())
    {
      messaget message(message_handler);
      message.error() << "location must have \"unsigned int\"" << messaget::eom;
      return true;
    }
    else
    {
      loc=safe_string2unsigned(std::string(loc_string, 0, std::string::npos));
    }

    if(!symbol_string.empty())
    {
      symbol_name=symbol_string;
      symbol_flag=true;
    }

    taint_data.add(loc, taint, symbol_flag, symbol_name);
  }

  return false;
}
