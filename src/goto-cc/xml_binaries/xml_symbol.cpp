/*******************************************************************\
 
Module: Compile and link source and object files.
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#include "xml_irep.h"
#include "xml_symbol.h"

/*******************************************************************\
 
Function: convert
 
  Inputs: a symbol and an xml node
 
 Outputs: none
 
 Purpose: converts a symbol to an xml symbol node
 
\*******************************************************************/

void convert(const symbolt& sym, xmlt &root)
{
  xmlt &xmlsym = root.new_element("symbol");
  xmlsym.set_attribute("name", id2string(sym.name));

  xmlt &xmltype = xmlsym.new_element("type");
  convert(sym.type, xmltype);

  xmlt &xmlval = xmlsym.new_element("value");
  if(!sym.is_type && sym.type.id() == "code" && !sym.value.is_nil())
    xmlval.data = "compiled"; // only for implemented functions
  else
    convert(sym.value, xmlval);

  xmlt &flags = xmlsym.new_element("flags");

  flags.set_attribute_bool("lvalue", sym.is_lvalue);
  flags.set_attribute_bool("static_lifetime", sym.is_static_lifetime);
  flags.set_attribute_bool("file_local", sym.is_file_local);
  flags.set_attribute_bool("theorem", sym.is_property);
  flags.set_attribute_bool("thread_local", sym.is_thread_local);
  flags.set_attribute_bool("type", sym.is_type);
  flags.set_attribute_bool("extern", sym.is_extern);
  flags.set_attribute_bool("input", sym.is_input);
  flags.set_attribute_bool("output", sym.is_output);
  flags.set_attribute_bool("macro", sym.is_macro);
  //flags.set_attribute_bool("actual", sym.is_actual);
  //flags.set_attribute_bool("binding", sym.binding);
  //flags.set_attribute_bool("free_var", sym.free_var);
  flags.set_attribute_bool("statevar", sym.is_state_var);

  xmlt &mode = flags.new_element("mode");
  mode.data = id2string(sym.mode);

  flags.new_element("base_name").data=id2string(sym.base_name);
  flags.new_element("module").data=id2string(sym.module);

  if (sym.pretty_name.size()>0)
    flags.new_element("pretty_name").data=id2string(sym.pretty_name);

  xmlt &xmlloc = xmlsym.new_element("location");
  convert(sym.location, xmlloc);
  xmlloc.name = "location"; // convert overwrote this
}

/*******************************************************************\
 
Function: convert
 
  Inputs: an xml node and a symbol
 
 Outputs: none
 
 Purpose: converts an xml symbol node to a symbol
 
\*******************************************************************/

void convert(const xmlt &xmlsym, symbolt& symbol)
{
  symbol.name=xmlsym.get_attribute("name");
  
  for(xmlt::elementst::const_iterator
      it=xmlsym.elements.begin();
      it!=xmlsym.elements.end();
      it++)
  {
    if (it->name=="type")
    {
      convert(*it, symbol.type);
    }
    else if (it->name=="value")
    {
      if (it->data=="compiled")
      {
        symbol.value.id("code");
      }
      else
      {
        convert(*it, symbol.value);
      }
    }
    else if (it->name=="flags")
    {
      symbol.is_lvalue = it->get_attribute_bool("lvalue");
      symbol.is_static_lifetime = it->get_attribute_bool("static_lifetime");
      symbol.is_file_local = it->get_attribute_bool("file_local");
      symbol.is_property = it->get_attribute_bool("theorem");
      symbol.is_thread_local = it->get_attribute_bool("thread_local");
      symbol.is_type = it->get_attribute_bool("type");
      symbol.is_extern = it->get_attribute_bool("extern");
      symbol.is_input = it->get_attribute_bool("input");
      symbol.is_output = it->get_attribute_bool("output");
      symbol.is_macro = it->get_attribute_bool("macro");
      //symbol.is_actual = it->get_attribute_bool("actual");
      //symbol.binding = it->get_attribute_bool("binding");
      //symbol.free_var = it->get_attribute_bool("free_var");
      symbol.is_state_var = it->get_attribute_bool("statevar");
      
      for(xmlt::elementst::const_iterator
          fit=it->elements.begin();
          fit!=it->elements.end();
          fit++)
      {
        if(fit->name=="mode")
          symbol.mode=fit->data;
        else if(fit->name=="base_name")
          symbol.base_name=fit->data;
        else if(fit->name=="module")
          symbol.module=fit->data;
      }
    }
    else if(it->name=="location")
    {
      convert(*it, symbol.location);
    }
  }
}
