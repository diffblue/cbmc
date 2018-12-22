/// \file linker_script_merge.h
/// \brief Merge linker script-defined symbols into a goto-program
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_GOTO_CC_LINKER_SCRIPT_MERGE_H
#define CPROVER_GOTO_CC_LINKER_SCRIPT_MERGE_H

#include <functional>

#include <util/cout_message.h>
#include <util/json.h>

#include "compile.h"
#include "gcc_cmdline.h"

/// \brief Patterns of expressions that should be replaced
///
/// Each instance of this class describes an expression 'shape' that should be
/// replaced with a different expression. The intention is that if some
/// expression matches the pattern described by this replacement_predicatet
/// (i.e. replacement_predicatet::match() returns true), then that expression
/// should be replaced by a new expression.
class replacement_predicatet
{
public:
  replacement_predicatet(
      const std::string &description,
      const std::function<const symbol_exprt&(const exprt&)> inner_symbol,
      const std::function<bool(const exprt&, const namespacet&)> match)
    : _description(description),
      _inner_symbol(inner_symbol),
      _match(match)
  {}

  /// \brief a textual description of the expression that we're trying to match
  const std::string &description() const
  {
    return _description;
  }

  /// \brief Return the underlying symbol of the matched expression
  /// \pre replacement_predicatet::match() returned true
  const symbol_exprt &inner_symbol(const exprt &expr) const
  {
    return _inner_symbol(expr);
  }

  /// \brief Predicate: does the given expression match an interesting pattern?
  ///
  /// If this function returns true, the entire expression should be replaced by
  /// a pointer whose underlying symbol is the symbol returned by
  /// replacement_predicatet::inner_symbol().
  bool match(const exprt &expr, const namespacet &ns) const
  {
    return _match(expr, ns);
  };

private:
  std::string _description;
  std::function<const symbol_exprt&(const exprt&)> _inner_symbol;
  std::function<bool(const exprt&, const namespacet&)> _match;
};

/// \brief Synthesise definitions of symbols that are defined in linker scripts
class linker_script_merget:public messaget
{
public:
  /// \brief Add values of linkerscript-defined symbols to the goto-binary
  /// \pre There is a single output file in each of `elf_binaries` and
  ///      `goto_binaries`, and the codebase is being linked with a custom
  ///      linker script passed to the compiler with the `-T` option.
  /// \post The `__CPROVER_initialize` function contains synthesized definitions
  ///       for all symbols that are declared in the C codebase and defined in
  ///       the linker script.
  /// \post All uses of these symbols throughout the code base are re-typed to
  ///       match the type of the synthesized definitions.
  /// \post The `__CPROVER_initialize` function contains one
  ///       `__CPROVER_allocated_memory` annotation for each object file section
  ///       that is specified in the linker script.
  int add_linker_script_definitions();

  typedef std::map<irep_idt, std::pair<symbol_exprt, exprt>> linker_valuest;

  linker_script_merget(
    compilet &,
    const std::string &elf_binary,
    const std::string &goto_binary,
    const cmdlinet &,
    message_handlert &);

protected:
  compilet &compiler;
  const std::string &elf_binary;
  const std::string &goto_binary;
  const cmdlinet &cmdline;

  /// \brief The "shapes" of expressions to be replaced by a pointer
  ///
  /// Whenever this linker_script_merget encounters an expression `expr` in the
  /// goto-program---if `rp.match(expr)` returns `true` for some `rp` in this
  /// list, and the underlying symbol of `expr` is a linker-defined symbol, then
  /// `expr` will be replaced by a pointer whose value is taken from the value
  /// in the linker script.
  std::list<replacement_predicatet> replacement_predicates;

  /// \brief Write linker script definitions to `linker_data`.
  int get_linker_script_data(
      std::list<irep_idt> &linker_defined_symbols,
      const symbol_tablet &symbol_table,
      const std::string &out_file,
      const std::string &def_out_file);

  /// \brief Write a list of definitions derived from `data` into gp's
  ///        `instructions` member.
  /// \pre `data` is in the format verified by #linker_data_is_malformed.
  /// \post For every memory region in `data`, a function call to
  ///       `__CPROVER_allocated_memory` is prepended to
  ///       `initialize_instructions`.
  /// \post For every symbol in `data`, a declaration and initialization of that
  ///       symbol is prepended to `initialize_instructions`.
  /// \post Every symbol in `data` shall be a key in `linker_values`; the value
  ///       shall be a constant expression with the actual value of the symbol
  ///       in the linker script.
  int ls_data2instructions(
    jsont &data,
    const std::string &linker_script,
    goto_programt &gp,
    symbol_tablet &symbol_table,
    linker_valuest &linker_values);

  /// \brief convert the type of linker script-defined symbols to `char*`
  ///
  /// #ls_data2instructions synthesizes definitions of linker script-defined
  /// symbols, and types those definitions as `char*`.  This means that if those
  /// symbols were declared extern with a different type throughout the target
  /// codebase, we need to change all expressions of those symbols to have type
  /// `char*` within the goto functions---as well as in the symbol table.
  ///
  /// The 'canonical' way for linker script-defined symbols to be declared
  /// within the codebase is as char[] variables, so we take care of converting
  /// those into char*s. However, the frontend occasionally converts expressions
  /// like &foo into &foo[0] (where foo is an array), so we have to convert
  /// expressions like that even when they don't appear in the original
  /// codebase.
  ///
  /// Note that in general, there is no limitation on what type a linker
  /// script-defined symbol should be declared as in the C codebase, because we
  /// should only ever be reading its address. So this function is incomplete in
  /// that it assumes that linker script-defined symbols have been declared as
  /// arrays in the C codebase. If a linker script-defined symbol is declared as
  /// some other type, that would likely need some custom logic to be
  /// implemented in this function.
  ///
  /// \post The types of linker-script defined symbols in the symbol table have
  ///       been converted to `char*`.
  /// \post Expressions of the shape `&foo[0]`, `&foo`, and `foo`, where `foo`
  ///       is a linker-script defined symbol with type array, have been
  ///       converted to `foo` whose type is `char*`.
  int pointerize_linker_defined_symbols(goto_modelt &, const linker_valuest &);

  /// \param expr: an expr whose subexpressions may need to be pointerized
  /// \param to_pointerize: The symbols that are contained in the subexpressions
  ///   that we will pointerize.
  /// \param linker_values: the names of symbols defined in linker scripts.
  /// \param ns: a namespace to look up types.
  ///
  /// The subexpressions that we pointerize should be in one-to-one
  /// correspondence with the symbols in `to_pointerize`. Every time we
  /// pointerize an expression containing a symbol in `to_pointerize`, we remove
  /// that symbol from `to_pointerize`. Therefore, when this function returns,
  /// `to_pointerize` should be empty. If it is not, then the symbol is
  /// contained in a subexpression whose shape is not recognised.
  int pointerize_subexprs_of(
      exprt &expr,
      std::list<symbol_exprt> &to_pointerize,
      const linker_valuest &linker_values,
      const namespacet &ns);

  /// \brief do the actual replacement of an expr with a new pointer expr
  int replace_expr(
      exprt &old_expr,
      const linker_valuest &linker_values,
      const symbol_exprt &old_symbol,
      const irep_idt &ident,
      const std::string &shape);

  /// \brief fill `to_pointerize` with names of linker symbols appearing in expr
  void symbols_to_pointerize(
      const linker_valuest &linker_values,
      const exprt &expr,
      std::list<symbol_exprt> &to_pointerize) const;

  /// \brief one-to-one correspondence between extern & linker symbols
  ///
  /// Check that a string is in `linker_defined_symbols` iff it is a key in the
  /// `linker_values` map. The error messages of this function describe what it
  /// means for this constraint to be violated.
  ///
  /// \param linker_defined_symbols: the list of symbols that were extern with
  ///   no value in the goto-program
  /// \param linker_values: map from the names of linker-defined symbols from
  ///   the object file, to synthesized values for those linker symbols.
  int goto_and_object_mismatch(
      const std::list<irep_idt> &linker_defined_symbols,
      const linker_valuest &linker_values);

  /// \brief Validate output of the `scripts/ls_parse.py` tool
  int linker_data_is_malformed(const jsont &data) const;
};

#endif // CPROVER_GOTO_CC_LINKER_SCRIPT_MERGE_H
