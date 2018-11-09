/*******************************************************************\

Module: SMT2 solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Abstract Syntax Tree for SMT2

#ifndef CPROVER_SOLVERS_SMT2_SMT2_AST_H
#define CPROVER_SOLVERS_SMT2_SMT2_AST_H

#include <functional>
#include <iterator>

#include <util/invariant.h>
#include <util/irep.h>
#include <util/mp_arith.h>
#include <util/optional.h>

/// Base class for Abstract Syntax Tree of SMT2 expressions.
/// Instances of this class are:
///   - \ref smt2_constantt with id \c ID_constant,
///   - \ref smt2_binary_literalt, special case of \ref smt2_constantt
///   - \ref smt2_symbolt, with id \c ID_symbol
///   - \ref smt2_string_literalt with id \c ID_string_constant
///   - \ref smt2_identifiert with id \c ID_identifier
///   - \ref smt2_sortt with with id \c ID_type
///   - \ref smt2_function_applicationt with id \c ID_function_application
///   - \ref smt2_listt with id \c ID_tuple
///   - \ref smt2_pairt, special case of \ref smt2_listt with exactly 2 elements
///   - \ref smt2_non_empty_listt, special case of \ref smt2_listt with at least
///     one element
///   - \ref smt2_forallt with id \c ID_forall
///   - \ref smt2_existst with id \c ID_exists
///   - \ref smt2_lett with id \c ID_let
///   - \ref smt2_sort_declarationt, special case of \ref smt2_pairt
///   - \ref smt2_selector_declarationt, special case of \ref smt2_pairt
///   - \ref smt2_constructor_declarationt with id \c ID_declaration
///   - \ref smt2_datatype_declarationt with id \c ID_par
class smt2_astt : public non_sharing_treet<smt2_astt, optionalt<irep_idt>>
{
public:
  /// Empty constructor
  smt2_astt() : tree_implementationt(irep_idt())
  {
  }

  const irep_idt &id() const
  {
    return read().data;
  }

  explicit smt2_astt(irep_idt id) : tree_implementationt(std::move(id))
  {
  }
};

std::ostream &operator<<(std::ostream &stream, const smt2_astt &ast);

class smt2_constantt : public smt2_astt
{
public:
  /// Make an AST representing a integer literal
  static smt2_constantt make(const mp_integer &m)
  {
    return smt2_constantt(integer2string(m));
  }

protected:
  explicit smt2_constantt(irep_idt value) : smt2_astt(ID_constant)
  {
    write().named_sub = std::move(value);
  }
};

class smt2_binary_literalt : public smt2_constantt
{
public:
  /// Make an AST representing a integer literal
  static smt2_binary_literalt make(const mp_integer &m)
  {
    return smt2_binary_literalt(integer2string(m, 2));
  }

  /// Takes a string in binary
  explicit smt2_binary_literalt(const irep_idt &m)
    : smt2_constantt("#b" + id2string(m))
  {
  }
};

class smt2_symbolt : public smt2_astt
{
public:
  explicit smt2_symbolt(irep_idt symbol) : smt2_astt(ID_symbol)
  {
    write().named_sub = std::move(symbol);
  }
};

class smt2_string_literalt : public smt2_astt
{
public:
  explicit smt2_string_literalt(irep_idt literal)
    : smt2_astt(ID_string_constant)
  {
    write().named_sub = std::move(literal);
  }
};

class smt2_identifiert : public smt2_astt
{
public:
  /// Identifiers are either symbols, or indexed: `( _ <symbol> <numeral>+ )`
  explicit smt2_identifiert(smt2_symbolt sym) : smt2_astt(std::move(sym))
  {
  }

  smt2_identifiert(smt2_symbolt sym, std::vector<smt2_constantt> indexes)
    : smt2_astt(ID_identifier)
  {
    auto &subs = write().sub;
    subs.emplace_back(std::move(sym));
    std::move(indexes.begin(), indexes.end(), std::back_inserter(subs));
  }
};

class smt2_sortt : public smt2_astt
{
public:
  static smt2_sortt Bool()
  {
    return smt2_sortt(smt2_symbolt{"Bool"});
  }

  static smt2_sortt Int()
  {
    return smt2_sortt(smt2_symbolt{"Int"});
  }

  static smt2_sortt Real()
  {
    return smt2_sortt(smt2_symbolt{"Real"});
  }

  static smt2_sortt BitVec(const mp_integer &i)
  {
    return smt2_sortt{
      smt2_identifiert{smt2_symbolt("BitVec"), {smt2_constantt::make(i)}}, {}};
  }

  explicit smt2_sortt(smt2_symbolt symbol)
    : smt2_astt(smt2_identifiert{std::move(symbol)})
  {
  }

  explicit smt2_sortt(smt2_identifiert identifier)
    : smt2_astt(std::move(identifier))
  {
  }

  smt2_sortt(smt2_identifiert identifier, std::vector<smt2_sortt> &&parameters);
};

class smt2_function_applicationt : public smt2_astt
{
public:
  explicit smt2_function_applicationt(
    smt2_identifiert sym,
    std::vector<smt2_astt> &&args)
    : smt2_astt(ID_function_application)
  {
    auto &subs = write().sub;
    subs.emplace_back(std::move(sym));
    std::move(args.begin(), args.end(), std::back_inserter(subs));
  }

  void add_argument(smt2_astt arg)
  {
    write().sub.emplace_back(std::move(arg));
  }
};

template <typename underlyingt>
class smt2_listt : public smt2_astt
{
  static_assert(
    std::is_base_of<smt2_astt, underlyingt>::value,
    "smt2_listt should contain smt2_astt elements");

public:
  explicit smt2_listt(std::vector<underlyingt> &&list) : smt2_astt(ID_tuple)
  {
    std::move(list.begin(), list.end(), std::back_inserter(write().sub));
  }
};

template <typename firstt, typename secondt>
class smt2_pairt : public smt2_listt<smt2_astt>
{
public:
  explicit smt2_pairt(firstt first, secondt second) : smt2_listt<smt2_astt>({})
  {
    auto &subs = write().sub;
    subs.push_back(std::move(first));
    subs.push_back(std::move(second));
  }

  const firstt &first() const
  {
    return static_cast<const firstt &>(read().sub[0]);
  }

  const smt2_sortt &second() const
  {
    return static_cast<const secondt &>(read().sub[1]);
  }
};

template <typename underlyingt>
class smt2_non_empty_listt : public smt2_listt<underlyingt>
{
public:
  explicit smt2_non_empty_listt(
    underlyingt head,
    std::vector<underlyingt> &&tail)
    : smt2_listt<underlyingt>({std::move(head)})
  {
    std::move(
      tail.begin(), tail.end(), std::back_inserter(smt2_astt::write().sub));
  }
};

class smt2_forallt : public smt2_astt
{
public:
  explicit smt2_forallt(
    smt2_listt<smt2_pairt<smt2_symbolt, smt2_sortt>> variables,
    smt2_astt expr)
    : smt2_astt(ID_forall)
  {
    auto &subs = write().sub;
    subs.emplace_back(std::move(variables));
    subs.emplace_back(std::move(expr));
  }
};

class smt2_existst : public smt2_astt
{
public:
  explicit smt2_existst(
    smt2_listt<smt2_pairt<smt2_symbolt, smt2_sortt>> variables,
    smt2_astt expr)
    : smt2_astt(ID_exists)
  {
    auto &subs = write().sub;
    subs.emplace_back(std::move(variables));
    subs.emplace_back(std::move(expr));
  }
};

class smt2_lett : public smt2_astt
{
public:
  explicit smt2_lett(
    smt2_listt<smt2_pairt<smt2_symbolt, smt2_astt>> variables,
    smt2_astt expr)
    : smt2_astt(ID_let)
  {
    subt &subs = write().sub;
    subs.emplace_back(std::move(variables));
    subs.emplace_back(std::move(expr));
  }
};

using smt2_sort_declarationt = smt2_pairt<smt2_symbolt, smt2_constantt>;
using smt2_selector_declarationt = smt2_pairt<smt2_symbolt, smt2_sortt>;

class smt2_constructor_declarationt : public smt2_astt
{
public:
  explicit smt2_constructor_declarationt(
    smt2_symbolt symbol,
    std::vector<smt2_selector_declarationt> selector_decs)
    : smt2_astt(ID_declaration)
  {
    auto sub = write().sub;
    sub.push_back(std::move(symbol));
    std::move(
      selector_decs.begin(), selector_decs.end(), std::back_inserter(sub));
  }
};

class smt2_datatype_declarationt : public smt2_astt
{
public:
  explicit smt2_datatype_declarationt(
    smt2_non_empty_listt<smt2_symbolt> symbols,
    smt2_non_empty_listt<smt2_constructor_declarationt> selector_decs)
    : smt2_astt(ID_par)
  {
    auto sub = write().sub;
    sub.push_back(std::move(symbols));
    sub.push_back(std::move(selector_decs));
  }
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_AST_H
