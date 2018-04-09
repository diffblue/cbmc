/*******************************************************************\

Module: binary irep conversions with hashing

Author: CM Wintersteiger

Date: May 2007

\*******************************************************************/

/// \file
/// binary irep conversions with hashing

#include "irep_serialization.h"

#include <sstream>
#include <iostream>

#include "string_hash.h"

irep_serialization_errort::irep_serialization_errort(const std::string &error):
  std::runtime_error(error)
{
}

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

void irep_serializationt::reference_convert(
  std::istream &in,
  irept &irep)
{
  std::size_t id=read_gb_word(in);

  if(id<ireps_container.ireps_on_read.size() &&
     ireps_container.ireps_on_read[id].first)
  {
    irep=ireps_container.ireps_on_read[id].second;
  }
  else
  {
    read_irep(in, irep);
    insert_on_read(id, irep);
  }
}

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
    std::cerr << "irep not terminated\n";
    throw 0;
  }
}

void irep_serializationt::reference_convert(
  const irept &irep,
  std::ostream &out)
{
  std::size_t h=ireps_container.irep_full_hash_container.number(irep);

  // should be merged with insert
  ireps_containert::ireps_on_writet::const_iterator fi=
    ireps_container.ireps_on_write.find(h);

  if(fi==ireps_container.ireps_on_write.end())
  {
    size_t id=insert_on_write(h);
    write_gb_word(out, id);
    write_irep(out, irep);
  }
  else
  {
    write_gb_word(out, fi->second);
  }
}

/// inserts an irep into the hashtable
/// \par parameters: a size_t and an irep
/// \return true on success, false otherwise
std::size_t irep_serializationt::insert_on_write(std::size_t h)
{
  std::pair<ireps_containert::ireps_on_writet::const_iterator, bool> res=
    ireps_container.ireps_on_write.insert(
      std::make_pair(h, ireps_container.ireps_on_write.size()));

  if(!res.second)
    return ireps_container.ireps_on_write.size();
  else
    return res.first->second;
}

/// inserts an irep into the hashtable, but only the id-hashtable (only to be
/// used upon reading ireps from a file)
/// \par parameters: a size_t and an irep
/// \return true on success, false otherwise
std::size_t irep_serializationt::insert_on_read(
  std::size_t id,
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
      std::pair<bool, irept>(true, i);
  }

  return id;
}

/// outputs 4 characters for a long, most-significant byte first
/// \par parameters: an output stream and a number
/// \return nothing
void write_gb_word(std::ostream &out, std::size_t u)
{
  // we write 7 bits each time, until we have zero

  while(true)
  {
    unsigned char value=u&0x7f;
    u>>=7;

    if(u==0)
    {
      out.put(value);
      break;
    }

    out.put(value | 0x80);
  }
}

/// reads 4 characters and builds a long int from them
/// \par parameters: a stream
/// \return a long
std::size_t irep_serializationt::read_gb_word(std::istream &in)
{
  std::size_t res=0;

  unsigned shift_distance=0;

  while(in.good())
  {
    unsigned char ch=static_cast<unsigned char>(in.get());
    res|=(size_t(ch&0x7f))<<shift_distance;
    shift_distance+=7;
    if((ch&0x80)==0)
      break;
  }

  return res;
}

/// outputs the string and then a zero byte.
/// \par parameters: an output stream and a string
/// \return nothing
void write_gb_string(std::ostream &out, const std::string &s)
{
  for(std::string::const_iterator it=s.begin();
      it!=s.end();
      ++it)
  {
    if(*it==0 || *it=='\\')
      out.put('\\'); // escape specials
    out << *it;
  }

  out.put(0);
}

/// reads a string from the stream
/// \par parameters: a stream
/// \return a string
irep_idt irep_serializationt::read_gb_string(std::istream &in)
{
  char c='\0';
  size_t length=0;

  while((c=static_cast<char>(in.get()))!=0)
  {
    if(!in.good())
    {
      throw irep_serialization_errort(
        "found non-null-terminated string while parsing input");
    }

    if(length>=read_buffer.size())
      read_buffer.resize(read_buffer.size()*2, 0);

    if(c=='\\') // escaped chars
      read_buffer[length]=static_cast<char>(in.get());
    else
      read_buffer[length]=c;

    length++;
  }

  return irep_idt(std::string(read_buffer.data(), length));
}

/// outputs the string reference
/// \par parameters: an output stream and a string
/// \return nothing
void irep_serializationt::write_string_ref(
  std::ostream &out,
  const irep_idt &s)
{
  size_t id=irep_id_hash()(s);
  if(id>=ireps_container.string_map.size())
    ireps_container.string_map.resize(id+1, false);

  if(ireps_container.string_map[id])
    write_gb_word(out, id);
  else
  {
    ireps_container.string_map[id]=true;
    write_gb_word(out, id);
    write_gb_string(out, id2string(s));
  }
}

/// reads a string reference from the stream
/// \par parameters: a stream
/// \return a string
irep_idt irep_serializationt::read_string_ref(std::istream &in)
{
  std::size_t id=read_gb_word(in);

  if(id>=ireps_container.string_rev_map.size())
    ireps_container.string_rev_map.resize(1+id*2,
      std::pair<bool, irep_idt>(false, irep_idt()));

  if(ireps_container.string_rev_map[id].first)
  {
    return ireps_container.string_rev_map[id].second;
  }
  else
  {
    irep_idt s=read_gb_string(in);
    ireps_container.string_rev_map[id]=
      std::pair<bool, irep_idt>(true, s);
    return ireps_container.string_rev_map[id].second;
  }
}
