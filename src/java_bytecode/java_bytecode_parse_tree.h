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
    locationt location;
    unsigned address;
    irep_idt statement, argument;
  };
  
  class membert
  {
  public:
    typet type;
    code_typet::parameterst parameters;
    irep_idt name;
    bool method;
    
    typedef std::vector<instructiont> instructionst;
    instructionst instructions;
    
    instructiont &add_instruction()
    {
      instructions.push_back(instructiont());
      return instructions.back();
    }

    void output(std::ostream &out) const;
    
    inline membert():method(false)
    {
    }
  };
  
  class classt
  {
  public:
    irep_idt name;
    irep_idt extends;
    
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
  
  static void output_type(const typet &, std::ostream &out);
};

#endif
