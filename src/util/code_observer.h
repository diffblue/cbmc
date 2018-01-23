/*******************************************************************\

Module: Misc Utilities

Author: Kurt Degiorgio

\*******************************************************************/

/// \file
/// code_observer.h

/// This file contains a couple of utility classes that should be used when one
/// needs to read all codet's of a particular type from a given symbol
/// table.  This saves you from having to manually iterate through the symbol
/// table.  These classes essentially implement the observable pattern.
///
/// In general, you first register one or more observers with
/// const_code_observert. The observer is a callback that is
/// associated with a specific irep_idt. This is used to determine for which
/// codet's the observer will be notified. The second step involves calling
/// visit_symbols which will in turn iterate through every codet inside the
/// given symbol-table and notify registered observers only if the id of the
/// codet in question matches the associated id of the observer.
///
/// Example: Examining all codet(ID_function_call)
///
/// \code
///
/// void A::examine_function_calls(const codet &code)
/// {
///   PRECONDITION(code.get_statement()==ID_function_call);
///   ...
/// }
///
/// ...
///
/// const_code_observert code_observer;
/// code_observer.register_observer(ID_function_call,
///     &A::examine_function_calls,
///     this,
///     std::placeholders::_1);
/// code_observer.visit_symbols(symbol_table);
///
/// ...
///
/// \endcode
///
/// Note: each unique irep_idt can only be associated with one observer.
///
/// Note': Currently there is only a const version of the codet observer. This
/// is due to limitations with the symbol table API, specifically the lack of a
/// publicly visible non-const iterator. If the codet needs to be modified then
/// inside the observer callback use symbol_table_baset::get_writeable_ref to
/// get a non-const handle and walk down the tree again.

#ifndef CPROVER_UTIL_CODE_OBSERVER_H
#define CPROVER_UTIL_CODE_OBSERVER_H

#include <unordered_map>
#include <functional>
#include <type_traits>

#include "symbol_table.h"
#include "std_code.h"

/// \brief base class for all code observer implementations
template <class T> class code_observer_baset
{
  static_assert(
    std::is_base_of<codet, T>::value,
    "T is not derived from codet");

public:
  virtual ~code_observer_baset() = default;

  /// registers an observer that is associated with specific codet id.
  /// \param id: id of the codet to be registered
  /// \param f: observer callback that is associated with the given, \p id
  /// \param args: arguments associated with the given callback, \p f, this
  //   should include  a placeholder object (std::placeholder_1), as the first
  //   argument.
  template <class F, class... Args>
  void register_observer(const irep_idt &id, const F &&f, Args &&... args)
  {
    auto observer = std::bind(f, args...);
    code_observers_map.insert({id, observer});
  }

protected:
  /// notifies (if any) the observer that is registered to receive a callback
  /// for the given codet, \p code
  /// \param code: will be passed to the registered observer that
  /// that has the same associated id
  void notify(T &code) const
  {
    auto it = code_observers_map.find(code.get_statement());
    if(it != code_observers_map.end())
      it->second(code);
  }

private:
  using observerst = std::function<void(T &)>;
  using code_observer_mapt =
    std::unordered_map<const irep_idt, const observerst, irep_id_hash>;
  code_observer_mapt code_observers_map;
};

/// \brief codet observer, used to get a callback for every
///   codet of a specfic type from a given symbol-table.
class const_code_observert final : private const_expr_visitort,
                                   public code_observer_baset<const codet>
{
public:
  /// iterates through a given symbol table and for every symbol calls its
  /// associated expression visitor
  /// \param symbol_table: symbol table to visit
  void visit_symbols(const symbol_tablet &symbol_table)
  {
    forall_symbols(it, symbol_table.symbols)
    {
      it->second.value.visit(*this);
    }
  }

  /// Called by expr_vistort, for every expression found. Expressions that are
  /// not of type ID_code are ignored. Otherwise, this function will notify
  /// the observer (if any) that is associated with this code type.
  /// \param expr: expression
  void operator()(const exprt &expr) override
  {
    if(expr.id() == ID_code)
      notify(to_code(expr));
  }
};

#endif // CPROVER_UTIL_CODE_OBSERVER_H
