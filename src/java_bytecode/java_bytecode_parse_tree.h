/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_PARSE_TREE_H
#define CPROVER_JAVA_BYTECODE_PARSE_TREE_H

#include <util/std_code.h>
#include <util/std_types.h>

class java_bytecode_parse_treet
{
public:
  class instructiont
  {
  public:
    source_locationt source_location;
    unsigned address;
    irep_idt statement;
    std::vector<exprt> args;
  };
  
  class membert
  {
  public:
    std::string signature;
    irep_idt base_name, name;
    bool is_method, is_static, is_native, is_abstract, is_public;

    typedef std::vector<instructiont> instructionst;
    instructionst instructions;
    
    instructiont &add_instruction()
    {
      instructions.push_back(instructiont());
      return instructions.back();
    }

    void output(std::ostream &out) const;
    
    inline membert():is_method(false), is_static(false), is_native(false), is_abstract(false),
                     is_public(false)
    {
    }
  };
  
  class classt
  {
  public:
    irep_idt name, extends;
    bool is_abstract;
    typedef std::list<irep_idt> implementst;
    implementst implements;
    
    typedef std::list<membert> memberst;
    memberst members;
    
    inline membert &add_member()
    {
      members.push_back(membert());
      return members.back();
    }

    void output(std::ostream &out) const;
    
    void swap(classt &other);
  };
  
  classt parsed_class;
  
  void swap(java_bytecode_parse_treet &other)
  {
    other.parsed_class.swap(parsed_class);
    other.class_refs.swap(class_refs);
  }

  inline void output(std::ostream &out) const
  {
    parsed_class.output(out);
  }

  typedef std::vector<irep_idt> class_refst;
  class_refst class_refs;
};

#endif
