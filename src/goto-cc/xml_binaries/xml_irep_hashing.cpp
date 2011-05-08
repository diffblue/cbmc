/*******************************************************************\
 
Module: XML-irep conversions with hashing
 
Author: CM Wintersteiger
 
Date: July 2006
 
\*******************************************************************/

#include <sstream>

#include "xml_irep_hashing.h" 
#include "string_hash.h"

/*******************************************************************\
 
Function: xml_irep_convertt::convert
 
  Inputs:
 
 Outputs:
 
 Purpose:
 
\*******************************************************************/

void xml_irep_convertt::convert(
  const irept &irep,
  xmlt &xml)
{  
  if(irep.id()!="nil")
    xml.new_element("id").data=irep.id_string();
    
  forall_irep(it, irep.get_sub())
  { 
    xmlt &x_sub=xml.new_element("s");
    reference_convert(*it, x_sub);
  }
  
  forall_named_irep(it, irep.get_named_sub())
  {
    xmlt &x_nsub=xml.new_element("ns");
    x_nsub.set_attribute("n", name2string(it->first));
    reference_convert(it->second, x_nsub);
  }
  
  forall_named_irep(it, irep.get_comments())
  {
    xmlt &x_com = xml.new_element("c");
    x_com.set_attribute("n", name2string(it->first));
    reference_convert(it->second, x_com);
  }
}

/*******************************************************************\
 
Function: xml_irep_convertt::convert
 
  Inputs:
 
 Outputs:
 
 Purpose:
 
\*******************************************************************/

void xml_irep_convertt::convert(
  const xmlt &xml,
  irept &irep)
{
  irep.id("nil");
  xmlt::elementst::const_iterator it = xml.elements.begin();  
  for (; it != xml.elements.end(); it++)
  {
    if (it->name=="R") {      
      irep.id("__REFERENCE__");
      irep.set("REF", it->data);
    } 
    else if (it->name=="id")
    {
      irep.id(it->data);
    }
    else if (it->name=="ns")
    {
      irept r;
      convert(*it, r);
      std::string named_name = it->get_attribute("n");
      irep.move_to_named_sub(named_name, r);
    }
    else if (it->name=="s")
    {
      irept r;
      convert(*it, r);
      irep.move_to_sub(r);
    }
    else if (it->name=="c")
    {
      irept r;
      convert(*it, r);
      std::string named_name = it->get_attribute("n");
      irep.move_to_named_sub(named_name, r);
    }
    else
    {
      // Should not happen
      std::cout << "Unknown sub found (" << it->name << "); malformed xml?";
      std::cout << std::endl;
    }
  }
}

/*******************************************************************\
 
Function: xml_irep_convertt::reference_convert
 
  Inputs:
 
 Outputs:
 
 Purpose:
 
\*******************************************************************/

void xml_irep_convertt::reference_convert(
  const irept &irep,
  xmlt &xml)
{
  xmlt &ir = xml.new_element("R");
  
  ireps_containert::content_containert::const_iterator fi = 
    find_irep_by_content(irep);
  if (fi==ireps_container.content_container.end()) 
  {           
    unsigned id = ireps_container.id_replace_map[add_with_childs(irep)];
    ir.data = long_to_string(id);
  } else {
    ir.data = long_to_string(
                ireps_container.id_replace_map[fi->second]);
  }
}

/*******************************************************************\
 
Function: xml_irep_convertt::add_with_childs
 
  Inputs:
 
 Outputs:
 
 Purpose:
 
\*******************************************************************/
unsigned long xml_irep_convertt::add_with_childs(const irept &iwi)
{
  unsigned long id = insert((unsigned long)&iwi, iwi);
  if (id!=(unsigned long)&iwi) return id;
  
  forall_irep(it, iwi.get_sub())
  {    
    ireps_containert::content_containert::const_iterator fi = 
      find_irep_by_content(*it);
    if (fi==ireps_container.content_container.end()) 
    { 
      add_with_childs(*it);
    }
  }
  forall_named_irep(it, iwi.get_named_sub())
  {    
    ireps_containert::content_containert::const_iterator fi = 
      find_irep_by_content(it->second);
    if (fi==ireps_container.content_container.end()) 
    { 
      add_with_childs(it->second);
    }
  }
  forall_named_irep(it, iwi.get_comments())
  {    
    ireps_containert::content_containert::const_iterator fi = 
      find_irep_by_content(it->second);
    if (fi==ireps_container.content_container.end()) 
    { 
      add_with_childs(it->second);
    }
  }  
  return id;
}

/*******************************************************************\

Function: xml_irep_convertt::resolve_references

  Inputs: none

 Outputs: none

 Purpose: resolves references to ireps from an irep after reading 
          an irep hash map into memory.

\*******************************************************************/

void xml_irep_convertt::resolve_references( const irept &cur )
{
  if (cur.id() == "__REFERENCE__")
  {
    unsigned long id = string_to_long(cur.get_string("REF"));
    ireps_containert::id_containert::const_iterator itr = find_irep_by_id(id);      
    if (itr==ireps_container.id_container.end()) 
    {
      std::cout << "Warning: can't resolve irep reference (sub " 
        << cur.get("REF") << ")" << std::endl;
    } 
    else 
    { 
      irept &curX = const_cast<irept&>(cur);                
      curX = itr->second;
    }
  }
    
  forall_irep(iti, cur.get_sub())
    resolve_references(*iti);
  
  forall_named_irep(iti, cur.get_named_sub())
    resolve_references(iti->second);
  
  forall_named_irep(iti, cur.get_comments())
    resolve_references(iti->second);     
        
}

/*******************************************************************\
 
Function: xml_irep_convertt::long_to_string
 
  Inputs: an irep pointer
 
 Outputs: a new string
 
 Purpose: converts the hash value to a readable string
 
\*******************************************************************/
std::string xml_irep_convertt::long_to_string(const unsigned long l) {
  std::stringstream s;
  s << std::hex << l;
  return s.str();
}

/*******************************************************************\
 
Function: xml_irep_convertt::string_to_long
 
  Inputs: a string
 
 Outputs: an unsigned long
 
 Purpose: converts the string to an unsigned long that used to give 
          a pointer to an irep in an old compilation
 
\*******************************************************************/
unsigned long xml_irep_convertt::string_to_long(const std::string &s) {
  std::stringstream ss(s);
  unsigned long res=0;
  ss >> std::hex >> res;
  return res;
}

/*******************************************************************\
 
Function: xml_irep_convertt::find_irep_by_id
 
  Inputs: an id
 
 Outputs: an iterator into the ireps hash set
 
 Purpose: finds an irep in the ireps hash set by its id
 
\*******************************************************************/
xml_irep_convertt::ireps_containert::id_containert::const_iterator 
xml_irep_convertt::find_irep_by_id(const unsigned int id) {
  return ireps_container.id_container.find(id);
}

/*******************************************************************\
 
Function: xml_irep_convertt::find_irep_by_content
 
  Inputs: an irep
 
 Outputs: an iterator into the ireps hash set
 
 Purpose: finds an irep in the ireps hash set by checking contents
 
\*******************************************************************/
xml_irep_convertt::ireps_containert::content_containert::const_iterator 
xml_irep_convertt::find_irep_by_content(const irept &irep) {
  return ireps_container.content_container.find(irep);
}

/*******************************************************************\
 
Function: xml_irep_convertt::insert
 
  Inputs: an unsigned long and an irep
 
 Outputs: true on success, false otherwise
 
 Purpose: inserts an irep into the hashtable 
 
\*******************************************************************/
unsigned long xml_irep_convertt::insert(
  unsigned long id, 
  const irept& i) 
{
  ireps_containert::content_containert::const_iterator sit;
  sit = find_irep_by_content(i);
  if (sit==ireps_container.content_container.end()) {
    ireps_container.content_container.insert(
      std::pair<irept, unsigned long>(i, id));
    
    if(  ireps_container.id_container.insert(
           std::pair<unsigned long, irept>(id, i)
         ).second ) {
      ireps_container.id_replace_map[id] = 
        ireps_container.id_container.size();
    }
        
    return id;
  } else {
    return sit->second;
  }      
}

/*******************************************************************\
 
Function: xml_irep_convertt::insert
 
  Inputs: a string and an irep
 
 Outputs: true on success, false otherwise
 
 Purpose: inserts an irep into the hashtable
 
\*******************************************************************/
unsigned long xml_irep_convertt::insert(
  const std::string &id, 
  const irept& i) 
{
  return insert(string_to_long(id), i);
}

/*******************************************************************\
 
Function: xml_irep_convertt::convert_map
 
  Inputs: an xml node
 
 Outputs: nothing
 
 Purpose: converts the current hash map of ireps into the given xml
          structure
 
\*******************************************************************/
void xml_irep_convertt::convert_map(xmlt &xml) {
  ireps_containert::id_containert::iterator hit = 
    ireps_container.id_container.begin();
  for (; hit!=ireps_container.id_container.end(); hit++) {
    xmlt &xmlhe = xml.new_element("irep");
    xmlhe.set_attribute("id", long_to_string(
                                ireps_container.id_replace_map[hit->first]));
    convert(hit->second, xmlhe);
  }
}

/*******************************************************************\
 
Function: xml_irep_convertt::output_map
 
  Inputs: an output stream
 
 Outputs: nothing
 
 Purpose: converts the current hash map of ireps into xml nodes and
          outputs them to the stream
 
\*******************************************************************/
void xml_irep_convertt::output_map(std::ostream &out, unsigned indent) {
  ireps_containert::id_containert::iterator hit = 
    ireps_container.id_container.begin();
  for (; hit!=ireps_container.id_container.end(); hit++) {
    xmlt xmlhe("irep");
    xmlhe.set_attribute("id", long_to_string(
                                ireps_container.id_replace_map[hit->first]));
    convert(hit->second, xmlhe);
    xmlhe.output(out, indent);   
  }
}
