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
  class itemt
  {
  public:
    irep_idt name;
    typet type;

    typedef std::vector<codet> instructionst;
    instructionst instructions;
  };
  
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
    bool is_method, is_static, is_native;

    typedef std::vector<instructiont> instructionst;
    instructionst instructions;
    
    instructiont &add_instruction()
    {
      instructions.push_back(instructiont());
      return instructions.back();
    }

    void output(std::ostream &out) const;
    
    inline membert():is_method(false), is_static(false), is_native(false)
    {
    }
  };
  
  class classt
  {
  public:
    irep_idt name, extends;
    
    typedef std::list<membert> memberst;
    memberst members;
    
    inline membert &add_member()
    {
      members.push_back(membert());
      return members.back();
    }

    void output(std::ostream &out) const;
  };
  
  typedef std::list<classt> classest;
  classest classes;
  
  inline classt &add_class()
  {
    classes.push_back(classt());
    return classes.back();
  }

  void swap(java_bytecode_parse_treet &other);
  void clear();
  void output(std::ostream &out) const;
};

#endif
