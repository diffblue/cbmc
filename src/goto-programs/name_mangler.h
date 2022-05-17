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
    std::vector<symbol_tablet::symbolst::const_iterator> old_syms;

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
      symbolt new_sym;
      new_sym = sym;
      new_sym.name = mangled;
      new_sym.is_file_local = false;

      new_syms.push_back(new_sym);
      old_syms.push_back(sym_it);

      rename.insert(sym.symbol_expr(), new_sym.symbol_expr());
      renamed_funs.insert(std::make_pair(sym.name, mangled));

      log.debug() << "Mangling: " << sym.name << " -> " << mangled << log.eom;
    }

    for(const auto &sym : new_syms)
      model.symbol_table.insert(sym);
    for(const auto &sym : old_syms)
      model.symbol_table.erase(sym);

    for(const auto &sym_pair : model.symbol_table)
    {
      const symbolt &sym = sym_pair.second;

      exprt e = sym.value;
      typet t = sym.type;
      if(rename(e) && rename(t))
        continue;

      symbolt &new_sym = model.symbol_table.get_writeable_ref(sym.name);
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
