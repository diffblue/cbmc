/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_ANSI_C_PARSER_H
#define CPROVER_ANSI_C_ANSI_C_PARSER_H

#include <cassert>
#include <set>

#include <util/parser.h>
#include <util/expr.h>
#include <util/string_hash.h>
#include <util/mp_arith.h>
#include <util/config.h>

#include "ansi_c_parse_tree.h"
#include "ansi_c_scope.h"

int yyansi_cparse();

class ansi_c_parsert:public parsert
{
public:
  ansi_c_parse_treet parse_tree;

  ansi_c_parsert()
    : tag_following(false),
      asm_block_following(false),
      parenthesis_counter(0),
      mode(modet::NONE),
      cpp98(false),
      cpp11(false),
      for_has_scope(false),
      ts_18661_3_Floatn_types(false)
  {
  }

  virtual bool parse() override
  {
    return yyansi_cparse()!=0;
  }

  virtual void clear() override
  {
    parsert::clear();
    parse_tree.clear();

    // scanner state
    tag_following=false;
    asm_block_following=false;
    parenthesis_counter=0;
    string_literal.clear();
    pragma_pack.clear();
    pragma_cprover.clear();

    // set up global scope
    scopes.clear();
    scopes.push_back(scopet());
  }

  // internal state of the scanner
  bool tag_following;
  bool asm_block_following;
  unsigned parenthesis_counter;
  std::string string_literal;
  std::list<exprt> pragma_pack;
  std::list<std::set<irep_idt>> pragma_cprover;

  typedef configt::ansi_ct::flavourt modet;
  modet mode;

  // recognize C++98 and C++11 keywords
  bool cpp98, cpp11;

  // in C99 and upwards, for(;;) has a scope
  bool for_has_scope;

  // ISO/IEC TS 18661-3:2015
  bool ts_18661_3_Floatn_types;

  typedef ansi_c_identifiert identifiert;
  typedef ansi_c_scopet scopet;

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

  enum class decl_typet { TAG, MEMBER, PARAMETER, OTHER };

  // convert a declarator and then add it to existing an declaration
  void add_declarator(exprt &declaration, irept &declarator);

  // adds a tag to the current scope
  void add_tag_with_body(irept &tag);

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
    const irep_idt &base_name, // in
    irep_idt &identifier, // out
    bool tag,
    bool label);

  static ansi_c_id_classt get_class(const typet &type);

  irep_idt lookup_label(const irep_idt base_name)
  {
    irep_idt identifier;
    lookup(base_name, identifier, false, true);
    return identifier;
  }

  void set_pragma_cprover()
  {
    source_location.remove(ID_pragma);
    for(const auto &pragma_set : pragma_cprover)
    {
      for(const auto &pragma : pragma_set)
        source_location.add_pragma(pragma);
    }
  }
};

extern ansi_c_parsert ansi_c_parser;

int yyansi_cerror(const std::string &error);
void ansi_c_scanner_init();

#endif // CPROVER_ANSI_C_ANSI_C_PARSER_H
