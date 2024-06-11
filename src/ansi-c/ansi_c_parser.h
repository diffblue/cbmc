/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_ANSI_C_PARSER_H
#define CPROVER_ANSI_C_ANSI_C_PARSER_H

#include <map>

#include <util/parser.h>
#include <util/config.h>

#include "ansi_c_parse_tree.h"
#include "ansi_c_scope.h"

class ansi_c_parsert;
int yyansi_cparse(ansi_c_parsert &);

class ansi_c_parsert:public parsert
{
public:
  ansi_c_parse_treet parse_tree;

  explicit ansi_c_parsert(message_handlert &message_handler)
    : parsert(message_handler),
      tag_following(false),
      asm_block_following(false),
      parenthesis_counter(0),
      mode(modet::NONE),
      cpp98(false),
      cpp11(false),
      for_has_scope(false),
      ts_18661_3_Floatn_types(false),
      __float128_is_keyword(false),
      float16_type(false),
      bf16_type(false),
      fp16_type(false)
  {
    // set up global scope
    scopes.clear();
    scopes.push_back(scopet());
  }

  bool parse() override
  {
    return yyansi_cparse(*this) != 0;
  }

  // internal state of the scanner
  bool tag_following;
  bool asm_block_following;
  unsigned parenthesis_counter;
  std::string string_literal;
  std::list<exprt> pragma_pack;

  typedef configt::ansi_ct::flavourt modet;
  modet mode;

  // recognize C++98 and C++11 keywords
  bool cpp98, cpp11;

  // in C99 and upwards, for(;;) has a scope
  bool for_has_scope;

  // ISO/IEC TS 18661-3:2015
  bool ts_18661_3_Floatn_types;
  bool __float128_is_keyword;
  bool float16_type;
  bool bf16_type;
  bool fp16_type;

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
    PRECONDITION(!scopes.empty());
    return scopes.back();
  }

  enum class decl_typet { TAG, MEMBER, PARAMETER, OTHER };

  // convert a declarator and then add it to existing an declaration
  void add_declarator(exprt &declaration, irept &declarator);

  // adds a tag to the current scope
  void add_tag_with_body(irept &tag);

  void copy_item(const ansi_c_declarationt &declaration)
  {
    PRECONDITION(declaration.id() == ID_declaration);
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

  /// \brief True iff the CPROVER pragma stack is empty
  bool pragma_cprover_empty();

  /// \brief Pushes an empty level in the CPROVER pragma stack
  void pragma_cprover_push();

  /// \brief Pops a level in the CPROVER pragma stack
  void pragma_cprover_pop();

  /// \brief Adds a check to the CPROVER pragma stack
  void pragma_cprover_add_check(const irep_idt &name, bool enabled);

  /// Returns true iff the same check with  polarity
  /// is already present at top of the stack
  bool pragma_cprover_clash(const irep_idt &name, bool enabled);

  /// \brief Tags \ref source_location with
  /// the current CPROVER pragma stack
  void set_pragma_cprover();

private:
  std::list<std::map<const irep_idt, bool>> pragma_cprover_stack;
};

void ansi_c_scanner_init(ansi_c_parsert &);

#endif // CPROVER_ANSI_C_ANSI_C_PARSER_H
