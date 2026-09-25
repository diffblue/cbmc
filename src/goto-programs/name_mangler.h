/// \file name_mangler.h
/// \brief Mangle names of file-local functions to make them unique
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_GOTO_PROGRAMS_NAME_MANGLER_H
#define CPROVER_GOTO_PROGRAMS_NAME_MANGLER_H

#include <util/message.h>
#include <util/rename_symbol.h>

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

    collect_file_local_functions(rename, renamed_funs, new_syms, old_syms);
    merge_into_symbol_table(new_syms, old_syms);
    apply_rename_to_symbols(rename);
    apply_rename_to_functions(rename);
    merge_into_function_map(renamed_funs);
  }

private:
  /// \brief Find all file-local functions and compute their mangled names
  ///
  /// Populates \p new_syms with the mangled symbols to be inserted, \p old_syms
  /// with the names of the original symbols to be removed, \p rename with the
  /// old-to-new symbol mapping, and \p renamed_funs with the old-to-new
  /// function-map name mapping.
  void collect_file_local_functions(
    rename_symbolt &rename,
    std::map<irep_idt, irep_idt> &renamed_funs,
    std::vector<symbolt> &new_syms,
    std::vector<irep_idt> &old_syms)
  {
    for(const auto &named_symbol : model.symbol_table.symbols)
    {
      const symbolt &sym = named_symbol.second;

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
  }

  /// \brief Insert the mangled symbols and remove the original ones
  ///
  /// If the mangled name already denotes a function declaration (no body), the
  /// declaration is updated in place with the definition. Its module and
  /// base_name are deliberately left untouched: both participate in
  /// symbol_tablet's indices and must not change after insertion (see
  /// symbol_tablet::validate()). Any other collision is reported as a warning.
  void merge_into_symbol_table(
    const std::vector<symbolt> &new_syms,
    const std::vector<irep_idt> &old_syms)
  {
    for(const auto &sym : new_syms)
    {
      auto result = model.symbol_table.insert(sym);
      if(!result.second)
      {
        symbolt &existing = result.first;
        if(existing.value.is_nil() && existing.type.id() == ID_code)
        {
          existing.type = sym.type;
          existing.value = sym.value;
          existing.is_file_local = sym.is_file_local;
          existing.mode = sym.mode;
          existing.location = sym.location;
          if(!sym.pretty_name.empty())
            existing.pretty_name = sym.pretty_name;
        }
        else
        {
          log.warning() << "Mangled name '" << sym.name
                        << "' already exists with a definition"
                        << messaget::eom;
        }
      }
    }
    for(const auto &name : old_syms)
      model.symbol_table.remove(name);
  }

  /// \brief Apply the renaming to the value and type of every symbol
  void apply_rename_to_symbols(const rename_symbolt &rename)
  {
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
  }

  /// \brief Apply the renaming to the bodies and parameter identifiers of all
  ///   functions
  void apply_rename_to_functions(const rename_symbolt &rename)
  {
    for(auto &fun : model.goto_functions.function_map)
    {
      if(!fun.second.body_available())
        continue;
      for(auto &identifier : fun.second.parameter_identifiers)
      {
        auto entry = rename.expr_map.find(identifier);
        if(entry != rename.expr_map.end())
          identifier = entry->second;
      }
      for(auto &ins : fun.second.body.instructions)
      {
        rename(ins.code_nonconst());
        if(ins.has_condition())
          rename(ins.condition_nonconst());
      }
    }
  }

  /// \brief Move each renamed function's body to its mangled name in the
  ///   function map
  ///
  /// If the mangled name already has an empty function-map entry (from a
  /// forward declaration), the definition's body is swapped in via
  /// goto_functiont::swap() (which also carries over function_is_hidden). The
  /// entry is looked up before the emplace so that the definition is not left
  /// moved-from on a colliding emplace; a pre-existing non-empty entry is
  /// reported at debug verbosity.
  void merge_into_function_map(const std::map<irep_idt, irep_idt> &renamed_funs)
  {
    for(const auto &pair : renamed_funs)
    {
      auto found = model.goto_functions.function_map.find(pair.first);
      INVARIANT(
        found != model.goto_functions.function_map.end(),
        "There should exist an entry in the function_map for the original name "
        "of the function that we renamed '" +
          std::string(pair.first.c_str()) + "'");

      auto existing = model.goto_functions.function_map.find(pair.second);
      if(existing == model.goto_functions.function_map.end())
      {
        model.goto_functions.function_map.emplace(
          pair.second, std::move(found->second));
      }
      else if(existing->second.body.instructions.empty())
      {
        existing->second.swap(found->second);
      }
      else
      {
        log.debug() << "Found a mangled name that already exists: "
                    << pair.second << messaget::eom;
      }

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
