/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_PARSER_H
#define CPROVER_ANSI_C_PARSER_H

#include <cassert>

#include <util/parser.h>
#include <util/expr.h>
#include <util/hash_cont.h>
#include <util/string_hash.h>
#include <util/i2string.h>
#include <util/mp_arith.h>

#include "ansi_c_parse_tree.h"

typedef enum { ANSI_C_UNKNOWN, ANSI_C_SYMBOL, ANSI_C_TYPEDEF,
               ANSI_C_TAG, ANSI_C_LOCAL_LABEL } ansi_c_id_classt;

int yyansi_cparse();

class ansi_c_parsert:public parsert
{
public:
  ansi_c_parse_treet parse_tree;
  
  ansi_c_parsert():
    cpp(false),
    for_has_scope(false)
  {
  }
  
  virtual bool parse()
  {
    return yyansi_cparse();
  }

  virtual void clear()
  {
    parsert::clear();
    parse_tree.clear();
    
    // scanner state
    tag_following=false;
    asm_block_following=false;
    parenthesis_counter=0;
    string_literal.clear();
    pragma_pack=0;
    
    // setup global scope
    scopes.clear();

    // this is the global scope
    scopes.push_back(scopet());
  }

  // internal state of the scanner
  bool tag_following;
  bool asm_block_following;
  unsigned parenthesis_counter;
  std::string string_literal;
  mp_integer pragma_pack;
  
  enum { LANGUAGE, EXPRESSION } grammar;

  enum { ANSI, GCC, MSC, ICC, CW, ARM } mode;
  // ANSI is strict ANSI-C
  // GCC is, well, gcc
  // MSC is Microsoft Visual Studio
  // ICC is Intel's C compiler
  // CW is CodeWarrior (with GCC extensions enabled)
  // ARM is ARM's RealView

  // recognize C++ keywords  
  bool cpp;
  
  // in C99 and upwards, for(;;) has a scope
  bool for_has_scope;

  class identifiert
  {
  public:
    ansi_c_id_classt id_class;
    irep_idt base_name;
    
    identifiert():id_class(ANSI_C_UNKNOWN)
    {
    }
  };
 
  class scopet
  {
  public:
    typedef hash_map_cont<irep_idt, identifiert, irep_id_hash> name_mapt;
    name_mapt name_map;
    
    std::string prefix;
    irep_idt last_declarator;
    
    // for(;;) and { } scopes are numbered
    unsigned compound_counter;
    unsigned anon_counter;
    
    scopet():compound_counter(0), anon_counter(0) { }
    
    void swap(scopet &scope)
    {
      name_map.swap(scope.name_map);
      prefix.swap(scope.prefix);
      last_declarator.swap(scope.last_declarator);
      std::swap(compound_counter, scope.compound_counter);
    }
    
    void print(std::ostream &out) const;
  };
   
  typedef std::list<scopet> scopest;
  scopest scopes;
  
  scopet &root_scope()
  {
    return scopes.front();
  }
  
  const scopet &root_scope() const
  {
    return scopes.front();
  }
  
  void pop_scope()
  {
    scopes.pop_back();
  }
   
  scopet &current_scope()
  {
    assert(!scopes.empty());
    return scopes.back();
  }

  static void convert_declarator(
    irept &declarator,
    const typet &type,
    irept &identifier);
    
  typedef enum { TAG, MEMBER, PARAMETER, OTHER } decl_typet;

  void new_declaration(
    const irept &type,
    irept &declarator,
    exprt &declaration,
    decl_typet decl_type);
   
  void copy_item(const ansi_c_declarationt &declaration)
  {
    assert(declaration.id()==ID_declaration);
    parse_tree.items.push_back(declaration);
  }
   
  void new_scope(const std::string &prefix)
  {
    const scopet &current=current_scope();
    scopes.push_back(scopet());
    scopes.back().prefix=current.prefix+prefix;
  }

  ansi_c_id_classt lookup(
    std::string &name,
    bool tag,
    bool label) const;

  static ansi_c_id_classt get_class(const typet &type);
  
  std::string get_anon_name()
  {
    std::string n="#anon";
    n+=i2string(current_scope().anon_counter++);
    return n;
  }
  
  irep_idt lookup_label(const irep_idt id)
  {
    std::string name=id2string(id);
    lookup(name, false, true);
    return name;
  }
};

extern ansi_c_parsert ansi_c_parser;

int yyansi_cerror(const std::string &error);
void ansi_c_scanner_init();

#endif
