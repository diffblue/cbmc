/*******************************************************************\
 
Module: binary irep conversions with hashing
 
Author: CM Wintersteiger
 
Date: May 2007
 
\*******************************************************************/

#include <sstream>
#include <iostream>

#include "irep_serialization.h" 
#include "string_hash.h"

/*******************************************************************\
 
Function: irep_serializationt::write_irep
 
  Inputs:
 
 Outputs:
 
 Purpose:
 
\*******************************************************************/

void irep_serializationt::write_irep(
  std::ostream &out,
  const irept &irep)
{ 
  write_string_ref(out, irep.id());
      
  forall_irep(it, irep.get_sub())
  { 
    out.put('S');    
    reference_convert(*it, out);
  }
    
  forall_named_irep(it, irep.get_named_sub())
  {
    out.put('N');
    write_string_ref(out, it->first);
    reference_convert(it->second, out);
  }
  
  forall_named_irep(it, irep.get_comments())
  {
    out.put('C');
    write_string_ref(out, it->first);
    reference_convert(it->second, out);
  }
  
  out.put(0); // terminator
}

/*******************************************************************\
 
Function: irep_serializationt::reference_convert
 
  Inputs:
 
 Outputs:
 
 Purpose:
 
\*******************************************************************/

void irep_serializationt::reference_convert(
  std::istream &in,
  irept &irep)
{
  unsigned id = read_long(in);
  
  if(id < ireps_container.ireps_on_read.size() && 
      ireps_container.ireps_on_read[id].first)
  {
    irep = ireps_container.ireps_on_read[id].second;
  }
  else
  {
    read_irep(in, irep);
    insert_on_read(id, irep);
  }
}

/*******************************************************************\
 
Function: irep_serializationt::read_irep
 
  Inputs:
 
 Outputs:
 
 Purpose:
 
\*******************************************************************/

void irep_serializationt::read_irep(
  std::istream &in,
  irept &irep)
{
  irep.clear();
  irep.id(read_string_ref(in));  
  
  while(in.peek()=='S')
  {
    in.get();
    irep.get_sub().push_back(irept());
    reference_convert(in, irep.get_sub().back());
  }
  
  while(in.peek()=='N')
  {
    in.get();
    irept &r=irep.add(read_string_ref(in));
    reference_convert(in, r);
  }
    
  while(in.peek()=='C')
  {
    in.get();
    irept &r=irep.add(read_string_ref(in));
    reference_convert(in, r);
  }
  
  if(in.get()!=0)
  {
    std::cerr << "irep not terminated. " << std::endl;
    throw 0;
  }
}

/*******************************************************************\
 
Function: irep_serializationt::reference_convert
 
  Inputs:
 
 Outputs:
 
 Purpose:
 
\*******************************************************************/

void irep_serializationt::reference_convert(
  const irept &irep,
  std::ostream &out)
{
  unsigned h=ireps_container.irep_full_hash_container.number(irep);

  // should be merged with insert
  ireps_containert::ireps_on_writet::const_iterator fi=
    ireps_container.ireps_on_write.find(h);

  if(fi==ireps_container.ireps_on_write.end()) 
  {         
    unsigned id=insert_on_write(h);
    write_long(out, id);
    write_irep(out, irep);
  }
  else
  {
    write_long(out, fi->second);
  }
}

/*******************************************************************\
 
Function: irep_serializationt::insert_on_write
 
  Inputs: an unsigned long and an irep
 
 Outputs: true on success, false otherwise
 
 Purpose: inserts an irep into the hashtable 
 
\*******************************************************************/

unsigned long irep_serializationt::insert_on_write(unsigned h) 
{
  std::pair<ireps_containert::ireps_on_writet::const_iterator,bool> res=
    ireps_container.ireps_on_write.insert(
      std::pair<unsigned, unsigned long>
      (h, ireps_container.ireps_on_write.size()));

  if(!res.second)
    return ireps_container.ireps_on_write.size();
  else
    return res.first->second;
}

/*******************************************************************\
 
Function: irep_serializationt::insert_on_read
 
  Inputs: an unsigned long and an irep
 
 Outputs: true on success, false otherwise
 
 Purpose: inserts an irep into the hashtable, but only the id-hashtable
          (only to be used upon reading ireps from a file) 
 
\*******************************************************************/

unsigned long irep_serializationt::insert_on_read(
  unsigned id,
  const irept &i)
{
  if(id>=ireps_container.ireps_on_read.size())
    ireps_container.ireps_on_read.resize(1+id*2, 
      std::pair<bool, irept>(false, get_nil_irep()));
    
  if(ireps_container.ireps_on_read[id].first)
    throw "irep id read twice.";
  else
  {
    ireps_container.ireps_on_read[id]=
      std::pair<bool,irept>(true, i);
  }  

  return id;
}

/*******************************************************************\
 
Function: write_long

  Inputs: an output stream and a number
 
 Outputs: nothing
 
 Purpose: outputs 4 characters for a long.
 
\*******************************************************************/

void write_long(std::ostream &out, unsigned u)
{
  out.put((u & 0xFF000000) >> 24); 
  out.put((u & 0x00FF0000) >> 16);
  out.put((u & 0x0000FF00) >> 8);
  out.put(u & 0x000000FF);
}

/*******************************************************************\
 
Function: irep_serializationt::read_long

  Inputs: a stream
 
 Outputs: a long
 
 Purpose: reads 4 characters and builds a long int from them
 
\*******************************************************************/

unsigned irep_serializationt::read_long(std::istream &in)
{
  unsigned res=0;

  for(unsigned i=0; i<4 && in.good(); i++)
    res = (res << 8) | in.get();

  return res;
}

/*******************************************************************\
 
Function: write_string

  Inputs: an output stream and a string
 
 Outputs: nothing
 
 Purpose: outputs the string and then a zero byte.
 
\*******************************************************************/

void write_string(std::ostream &out, const std::string &s)
{
  for (unsigned i=0; i<s.size(); i++)
  {
    if(s[i]==0 || s[i]=='\\') out.put('\\'); // escape specials 
    out << s[i];
  }

  out.put(0);
}

/*******************************************************************\
 
Function: irep_serializationt::read_string

  Inputs: a stream
 
 Outputs: a string
 
 Purpose: reads a string from the stream
 
\*******************************************************************/

irep_idt irep_serializationt::read_string(std::istream &in)
{  
  char c;
  unsigned i=0;

  while((c = in.get()) != 0)
  {
    if(i>=read_buffer.size())
      read_buffer.resize(read_buffer.size()*2, 0);

    if(c=='\\') // escaped chars
      read_buffer[i] = in.get();
    else
      read_buffer[i] = c;

    i++;    
  }

  if(i>=read_buffer.size())
    read_buffer.resize(read_buffer.size()*2, 0);

  read_buffer[i] = 0;

  return irep_idt(&(read_buffer[0]));
}

/*******************************************************************\
 
Function: irep_serializationt::write_string_ref

  Inputs: an output stream and a string
 
 Outputs: nothing
 
 Purpose: outputs the string reference
 
\*******************************************************************/

void irep_serializationt::write_string_ref( 
  std::ostream &out, 
  const irep_idt &s)
{
  unsigned id=irep_id_hash()(s);
  if(id>=ireps_container.string_map.size()) 
    ireps_container.string_map.resize(id+1, false);
     
  if(ireps_container.string_map[id])
    write_long(out, id);
  else
  {
    ireps_container.string_map[id]=true;
    write_long(out, id);
    write_string(out, id2string(s));
  }
}

/*******************************************************************\
 
Function: irep_serializationt::read_string_ref

  Inputs: a stream
 
 Outputs: a string
 
 Purpose: reads a string reference from the stream
 
\*******************************************************************/

irep_idt irep_serializationt::read_string_ref(std::istream &in)
{  
  unsigned id = read_long(in);
  
  if(id>=ireps_container.string_rev_map.size()) 
    ireps_container.string_rev_map.resize(1+id*2, 
      std::pair<bool,irep_idt>( false, irep_idt() ));

  if(ireps_container.string_rev_map[id].first)
  {
    return ireps_container.string_rev_map[id].second;
  }
  else
  {
    irep_idt s=read_string(in);
    ireps_container.string_rev_map[id] = 
      std::pair<bool,irep_idt>(true, s);
    return ireps_container.string_rev_map[id].second; 
  }
}
