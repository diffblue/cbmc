/*******************************************************************\
 
Module: binary irep conversions with hashing
 
Author: CM Wintersteiger
 
Date: May 2007
 
\*******************************************************************/

#ifndef IREP_SERIALIZATION_H_
#define IREP_SERIALIZATION_H_

#include <map>
#include <ostream>
#include <string>
#include <vector>

#include "irep_hash_container.h"
#include "irep.h"

void write_long(std::ostream &, unsigned); 
void write_string(std::ostream &, const std::string &);

class irep_serializationt
{
private:
  struct ul_hash
  {
    unsigned short operator()(const unsigned long l) const 
    { 
      return (l & 0xFFFF); 
    }
  };

  struct ul_eq
  {
    bool operator()(const unsigned long l, const unsigned long r) const 
    {
      return (l==r);
    }
  };

  struct irep_full_hash
  {
    size_t operator()(const irept &i) const 
    { 
      return i.full_hash(); 
    }
  };

  struct irep_content_eq
  {
    bool operator()(const irept &l, const irept &r) const 
    {
      return full_eq(l,r);
    }
  };
  
public:
  class ireps_containert
  {
  public:
    typedef std::vector<std::pair<bool, irept> > ireps_on_readt;
    ireps_on_readt ireps_on_read;

    irep_full_hash_containert irep_full_hash_container;
    typedef std::map<unsigned, unsigned long> ireps_on_writet;
    ireps_on_writet ireps_on_write;
    
    typedef std::vector<bool> string_mapt;
    string_mapt string_map;

    typedef std::vector<std::pair<bool, irep_idt> > string_rev_mapt;
    string_rev_mapt string_rev_map;
    
    void clear()
    { 
      irep_full_hash_container.clear();
      ireps_on_write.clear(); 
      ireps_on_read.clear();
      string_map.clear();
      string_rev_map.clear();
    }        
  };
  
  irep_serializationt(ireps_containert& ic): 
    ireps_container(ic) 
  { 
    read_buffer.resize(1, 0);
    clear(); 
  };
  
  unsigned long insert_on_write(unsigned h);
  unsigned long insert_on_read(unsigned id, const irept&);
  
  void reference_convert(std::istream&, irept &irep);
  void reference_convert(const irept &irep, std::ostream&);

  irep_idt read_string_ref( std::istream& );
  void write_string_ref( std::ostream&, const irep_idt& );

  void clear() { ireps_container.clear(); }

  static unsigned read_long( std::istream& );
  irep_idt read_string( std::istream& );

private:
  ireps_containert& ireps_container;
  std::vector<char> read_buffer;

  void write_irep(std::ostream&, const irept &irep);      
  void read_irep(std::istream&, irept &irep);
};

#endif /*IREP_SERIALIZATION_H_*/
