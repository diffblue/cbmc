/// \file name_mangler.h
/// \brief Mangle names of file-local functions to make them unique
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_GOTO_PROGRAMS_NAME_MANGLER_H
#define CPROVER_GOTO_PROGRAMS_NAME_MANGLER_H

#include <util/message.h>
#include <util/rename_symbol.h>
#include <util/std_types.h>

#include "goto_model.h"

#include <regex>
#include <vector>

#define FILE_LOCAL_PREFIX CPROVER_PREFIX "file_local_"

/// \brief Mangles the names in an entire program and its symbol table
///
/// The type parameter to this class should be a functor that has a no-arg
/// constructor and an `operator()` override with the following signature:
///
///     irep_idt operator()(const symbolt &, const std::string &);
///
/// The return type doesn't actually have to be an irep_idt, just something
/// that can be assigned to one. The function is expected to return the
/// mangled name of its \ref symbolt argument, incorporating the second
/// argument into the mangled name if possible.
template <class MangleFun>
class function_name_manglert
{
public:
  /// \param mh: handler to construct a log from
  /// \param gm: mangle all names in gm's symbol table and goto program
  /// \param extra_info: a string to be included in each mangled name
  function_name_manglert(
    message_handlert &mh,
    goto_modelt &gm,
    const std::string &extra_info)
    : log(mh), model(gm), mangle_fun(), extra_info(extra_info)
  {
  }

  /// \brief Mangle all file-local function symbols in the program
  ///
  /// The way in which the symbols will be mangled is decided by which mangler
  /// type this object is instantiated with, e.g. DJB_manglert mangles the path
  /// name by hashing it.
  void mangle()
  {
    rename_symbolt rename;
    std::map<irep_idt, irep_idt> renamed_funs;
    std::vector<symbolt> new_syms;
    std::vector<irep_idt> old_syms;

    for(auto sym_it = model.symbol_table.symbols.begin();
        sym_it != model.symbol_table.symbols.end();
        ++sym_it)
    {
      const symbolt &sym = sym_it->second;

      if(sym.type.id() != ID_code) // is not a function
        continue;
      if(sym.value.is_nil()) // has no body
        continue;
      if(!sym.is_file_local)
        continue;

      const irep_idt mangled = mangle_fun(sym, extra_info);
      symbolt new_sym = sym;
      new_sym.name = mangled;
      new_sym.base_name = mangled;
      if(new_sym.pretty_name.empty())
        new_sym.pretty_name = sym.base_name;
      new_sym.is_file_local = false;

      new_syms.push_back(new_sym);
      old_syms.push_back(sym.name);

      rename.insert(sym.symbol_expr(), new_sym.symbol_expr());
      renamed_funs.insert(std::make_pair(sym.name, mangled));

      log.debug() << "Mangling: " << sym.name << " -> " << mangled << log.eom;
    }

    // Second pass: rename scoped child symbols of renamed
    // functions.  Parameter symbols and function-local
    // variables are stored in the symbol table under names of
    // the form `<function_name>::<base_name>` (and longer
    // scope chains for nested locals).  Without renaming
    // these, two translation units that include the same
    // kernel header end up with identically-named parameter
    // symbols (e.g. `security_netlink_send::sk` from both
    // TUs); the linker then either accepts them with a
    // `$link1` suffix on one (unifying the function symbol
    // under its external name) or rejects them as
    // 'conflicting function declarations' depending on
    // whether the parameter types match exactly.  The fix is
    // to rename child symbols in lockstep with the parent
    // function so the per-TU mangling is complete.
    std::vector<symbolt> new_child_syms;
    std::vector<irep_idt> old_child_syms;
    for(const auto &sym_pair : model.symbol_table.symbols)
    {
      const std::string sym_name = id2string(sym_pair.first);
      // Child symbols are scoped as `<function>::<rest>`.  Renamed file-local
      // function names never contain "::" themselves (plain C file-local names
      // and the __CPROVER_file_local_<file>_<sym> mangling are "::"-free), so
      // the leading scope up to the first "::" is the owning function's name.
      // A single lookup then decides whether this symbol belongs to a renamed
      // function; this also subsumes skipping the function symbols themselves,
      // since those have no "::".
      const std::size_t sep = sym_name.find("::");
      if(sep == std::string::npos)
        continue;
      auto renamed = renamed_funs.find(sym_name.substr(0, sep));
      if(renamed == renamed_funs.end())
        continue;

      const irep_idt new_name =
        id2string(renamed->second) + sym_name.substr(sep);
      symbolt new_child = sym_pair.second;
      new_child.name = new_name;
      // Clear file_local on the child symbols too: the parent
      // function has just transitioned from file-local to
      // globally-mangled and unifiable, and the linker's
      // file-local renaming rule (RENAME_NEW for any
      // file_local symbol it sees on the new side of a link)
      // would otherwise force `$link1` suffixes on each
      // duplicate child symbol — defeating the unification we
      // just set up.  The new mangled name is unique across
      // TUs that share the header but should unify cleanly
      // when two TUs include the SAME header (because both
      // ends of the link produce identical mangled names).
      new_child.is_file_local = false;
      new_child_syms.push_back(new_child);
      old_child_syms.push_back(sym_pair.first);
      rename.insert(sym_pair.second.symbol_expr(), new_child.symbol_expr());
    }

    for(const auto &sym : new_syms)
      model.symbol_table.insert(sym);
    // Erase the originals by name (not by stored iterator): the inserts above
    // may have rehashed symbol_table.symbols, which would invalidate any held
    // iterators.  symbol_tablet::remove re-finds the entry, so it is safe.
    for(const auto &name : old_syms)
      model.symbol_table.remove(name);
    for(const auto &sym : new_child_syms)
      model.symbol_table.insert(sym);
    for(const auto &name : old_child_syms)
      model.symbol_table.remove(name);

    for(auto it = model.symbol_table.begin(); it != model.symbol_table.end();
        ++it)
    {
      const symbolt &sym = it->second;

      exprt e = sym.value;
      typet t = sym.type;
      if(rename(e) && rename(t))
        continue;

      symbolt &new_sym = it.get_writeable_symbol();
      new_sym.value = e;
      new_sym.type = t;
    }

    for(auto &fun : model.goto_functions.function_map)
    {
      if(!fun.second.body_available())
        continue;
      for(auto &ins : fun.second.body.instructions)
      {
        rename(ins.code_nonconst());
        if(ins.has_condition())
          rename(ins.condition_nonconst());
      }
    }

    // Add goto-programs with new function names
    for(const auto &pair : renamed_funs)
    {
      auto found = model.goto_functions.function_map.find(pair.first);
      INVARIANT(
        found != model.goto_functions.function_map.end(),
        "There should exist an entry in the function_map for the original name "
        "of the function that we renamed '" +
          std::string(pair.first.c_str()) + "'");

      auto inserted = model.goto_functions.function_map.emplace(
        pair.second, std::move(found->second));
      if(!inserted.second)
        log.debug() << "Found a mangled name that already exists: "
                    << std::string(pair.second.c_str()) << log.eom;

      // The moved goto_functiont still carries parameter_identifiers scoped
      // under the old function name; the rename above only updated the
      // identifiers embedded in the symbol's code_typet.  Re-derive the vector
      // from that (now renamed) code_typet so the in-memory model is
      // self-consistent -- otherwise goto_functionst::validate() and any
      // in-memory consumer would look up the stale `<old_func>::param` names.
      const symbolt &fun_sym = model.symbol_table.lookup_ref(pair.second);
      if(fun_sym.type.id() == ID_code)
        inserted.first->second.set_parameter_identifiers(
          to_code_type(fun_sym.type));

      model.goto_functions.function_map.erase(found);
    }
  }

protected:
  mutable messaget log;
  goto_modelt &model;
  MangleFun mangle_fun;
  const std::string &extra_info;
};

/// \brief Mangle identifiers by including their filename
class file_name_manglert
{
public:
  file_name_manglert()
    : forbidden("[^\\w]", std::regex::ECMAScript),
      multi_under("_+", std::regex::ECMAScript)
  {
  }
  irep_idt operator()(const symbolt &, const std::string &);

protected:
  const std::regex forbidden;
  const std::regex multi_under;
};

/// \brief Mangle identifiers by hashing their working directory with djb2 hash
///
/// Hashes emitted by objects of this class include the leading 8 digits of the
/// djb2 hash of the file path.
class djb_manglert
{
public:
  djb_manglert()
  {
  }
  irep_idt operator()(const symbolt &, const std::string &);
};

#endif // CPROVER_GOTO_PROGRAMS_NAME_MANGLER_H
