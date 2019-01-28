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

#include "exception_utils.h"
#include "string_hash.h"

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

    if(id >= ireps_container.ireps_on_read.size())
      ireps_container.ireps_on_read.resize(1 + id * 2, {false, get_nil_irep()});

    // guard against self-referencing ireps
    if(ireps_container.ireps_on_read[id].first)
      throw deserialization_exceptiont("irep id read twice.");

    ireps_container.ireps_on_read[id] = {true, irep};
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
    throw deserialization_exceptiont("irep not terminated");
  }
}

/// Serialize an irept
/// \param irep: source irept to serialize
/// \param out: target output stream
void irep_serializationt::reference_convert(
  const irept &irep,
  std::ostream &out)
{
  std::size_t h=ireps_container.irep_full_hash_container.number(irep);

  const auto res = ireps_container.ireps_on_write.insert(
    {h, ireps_container.ireps_on_write.size()});

  write_gb_word(out, res.first->second);
  if(res.second)
    write_irep(out, irep);
}

/// Write 7 bits of `u` each time, least-significant byte first, until we have
/// zero.
/// \param out: target stream
/// \param u: number to write
void write_gb_word(std::ostream &out, std::size_t u)
{

  while(true)
  {
    unsigned char value=u&0x7f;
    u>>=7;

    if(u==0)
    {
      out.put(static_cast<char>(value));
      break;
    }

    out.put(value | 0x80);
  }
}

/// Interpret a stream of byte as a 7-bit encoded unsigned number.
/// \param in: input stream
/// \return decoded number
std::size_t irep_serializationt::read_gb_word(std::istream &in)
{
  std::size_t res=0;

  unsigned shift_distance=0;

  while(in.good())
  {
    if(shift_distance >= sizeof(res) * 8)
      throw deserialization_exceptiont("input number too large");

    unsigned char ch=static_cast<unsigned char>(in.get());
    res|=(size_t(ch&0x7f))<<shift_distance;
    shift_distance+=7;
    if((ch&0x80)==0)
      break;
  }

  if(!in.good())
    throw deserialization_exceptiont("unexpected end of input stream");

  return res;
}

/// outputs the string and then a zero byte.
/// \param out: output stream
/// \param s: string to output
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
/// \param in: input stream
/// \return a string
irep_idt irep_serializationt::read_gb_string(std::istream &in)
{
  char c;
  size_t length=0;

  while((c=static_cast<char>(in.get()))!=0)
  {
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

/// Output a string and maintain a reference to it
/// \param out: output stream
/// \param s: string to output
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

/// Read a string reference from the stream
/// \param in: input stream
/// \return a string
irep_idt irep_serializationt::read_string_ref(std::istream &in)
{
  std::size_t id=read_gb_word(in);

  if(id>=ireps_container.string_rev_map.size())
    ireps_container.string_rev_map.resize(1+id*2,
      std::pair<bool, irep_idt>(false, irep_idt()));

  if(!ireps_container.string_rev_map[id].first)
  {
    irep_idt s=read_gb_string(in);
    ireps_container.string_rev_map[id]=
      std::pair<bool, irep_idt>(true, s);
  }

  return ireps_container.string_rev_map[id].second;
}
