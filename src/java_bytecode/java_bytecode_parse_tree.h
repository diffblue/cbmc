/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_PARSE_TREE_H
#define CPROVER_JAVA_BYTECODE_PARSE_TREE_H

#include <set>

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
    typedef std::vector<exprt> argst;
    argst args;
  };
  
  class membert
  {
  public:
    std::string signature;
    irep_idt name;
    bool is_public, is_protected, is_private, is_static, is_final;
    
    virtual void output(std::ostream &out) const = 0;
    
    inline membert():
      is_public(false), is_protected(false), is_private(false),
      is_static(false), is_final(false)
    {
    }
  };
  
  class methodt:public membert
  {
  public:
    irep_idt base_name;
    bool is_native, is_abstract, is_synchronized;

    typedef std::vector<instructiont> instructionst;
    instructionst instructions;
    
    instructiont &add_instruction()
    {
      instructions.push_back(instructiont());
      return instructions.back();
    }
    
    class exceptiont
    {
    };
    
    typedef std::vector<exceptiont> exception_tablet;
    exception_tablet exception_table;

    virtual void output(std::ostream &out) const;
    
    inline methodt():is_native(false), is_abstract(false), is_synchronized(false)
    {
    }
  };
  
  class fieldt:public membert
  {
  public:
    virtual void output(std::ostream &out) const;
  };
  
  class classt
  {
  public:
    irep_idt name, extends;
    bool is_abstract;
    typedef std::list<irep_idt> implementst;
    implementst implements;
    
    typedef std::list<fieldt> fieldst;
    typedef std::list<methodt> methodst;
    fieldst fields;
    methodst methods;
    
    inline fieldt &add_field()
    {
      fields.push_back(fieldt());
      return fields.back();
    }

    inline methodt &add_method()
    {
      methods.push_back(methodt());
      return methods.back();
    }

    void output(std::ostream &out) const;
    
    void swap(classt &other);
  };
  
  classt parsed_class;
  
  void swap(java_bytecode_parse_treet &other)
  {
    other.parsed_class.swap(parsed_class);
    other.class_refs.swap(class_refs);
    std::swap(loading_successful, other.loading_successful);
  }

  void output(std::ostream &out) const;

  typedef std::set<irep_idt> class_refst;
  class_refst class_refs;
  
  bool loading_successful;
  
  inline java_bytecode_parse_treet():loading_successful(false)
  {
  }
};

#endif
