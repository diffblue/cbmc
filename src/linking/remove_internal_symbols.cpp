/*******************************************************************\

Module: Remove symbols that are internal only

Author: Daniel Kroening

\*******************************************************************/

#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/find_symbols.h>
#include <util/std_types.h>
#include <util/cprover_prefix.h>
#include <util/message_stream.h>
#include <util/file_util.h>

#include "remove_internal_symbols.h"

/*******************************************************************\

Function: get_symbols_rec

  Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/

void get_symbols_rec(
  const namespacet &ns,
  const symbolt &symbol,
  find_symbols_sett &dest)
{
  if(!dest.insert(symbol.name).second)
    return;
  
  find_symbols_sett new_symbols;

  find_type_and_expr_symbols(symbol.type, new_symbols);
  find_type_and_expr_symbols(symbol.value, new_symbols);
  
  if(symbol.type.id()==ID_code)
  {
    const code_typet &code_type=to_code_type(symbol.type);
    const code_typet::parameterst &parameters=code_type.parameters();

    for(code_typet::parameterst::const_iterator
        it=parameters.begin();
        it!=parameters.end();
        it++)
    {
      irep_idt id=it->get_identifier();
      const symbolt *s;
      // identifiers for prototypes need not exist
      if(!ns.lookup(id, s)) new_symbols.insert(id);
    }
  }

  for(find_symbols_sett::const_iterator
      it=new_symbols.begin();
      it!=new_symbols.end();
      it++)
  {
    get_symbols_rec(ns, ns.lookup(*it), dest); // recursive call
  }
}

/*******************************************************************\

Function: remove_internal_symbols

  Inputs: symbol table

 Outputs: symbol table, with internal symbols removed

 Purpose: A symbol is EXPORTED if it is a
          * non-static function with body that is not extern inline
          * symbol used in an EXPORTED symbol
          * type used in an EXPORTED symbol
          
          Read
          http://gcc.gnu.org/ml/gcc/2006-11/msg00006.html
          on "extern inline"

\*******************************************************************/

void remove_internal_symbols(
  symbol_tablet &symbol_table,
  const include_mapt &include_map,
  message_handlert &message_handler)
{
  namespacet ns(symbol_table);
  find_symbols_sett exported;

  // we retain certain special ones
  find_symbols_sett special;
  special.insert("argc'");  
  special.insert("argv'");  
  special.insert("envp'");  
  special.insert("envp_size'");  
  special.insert(CPROVER_PREFIX "memory");  
  special.insert(CPROVER_PREFIX "initialize");
  special.insert(CPROVER_PREFIX "malloc_size");
  special.insert(CPROVER_PREFIX "deallocated");
  special.insert(CPROVER_PREFIX "dead_object");
  special.insert(CPROVER_PREFIX "rounding_mode");

  struct file_infot
  {
    file_infot():is_system_header(false), is_nested(false)
    {
    }

    bool is_system_header;
    bool is_nested;
    source_locationt included_from;
  };
  hash_map_cont<irep_idt, file_infot, irep_id_hash> unused_files;

  for(symbol_tablet::symbolst::const_iterator
      it=symbol_table.symbols.begin();
      it!=symbol_table.symbols.end();
      it++)
  {
    const symbolt &symbol=it->second;

    const irep_idt &f=symbol.location.get_file();
    if(!f.empty())
    {
      file_infot f_info;
      f_info.is_system_header=symbol.location.get_hide();

      include_mapt::const_iterator entry=include_map.find(f);
      if(entry!=include_map.end() &&
         !entry->second.get_file().empty())
      {
        f_info.included_from=entry->second;

        entry=include_map.find(entry->second.get_file());
        if(entry!=include_map.end() &&
           !entry->second.get_file().empty() &&
           !is_dot_i_file(id2string(entry->second.get_file())))
          f_info.is_nested=true;
      }

      unused_files.insert(std::make_pair(f, f_info));
    }

    if(special.find(symbol.name)!=special.end())
    {
      get_symbols_rec(ns, symbol, exported);
      continue;
    }
    
    bool is_function=symbol.type.id()==ID_code;
    bool is_file_local=symbol.is_file_local;
    bool is_type=symbol.is_type;
    bool has_body=symbol.value.is_not_nil();
    bool has_initializer=
      symbol.value.is_not_nil() &&
      !symbol.value.get_bool(ID_C_zero_initializer);

    // __attribute__((constructor)), __attribute__((destructor))
    if(symbol.mode==ID_C && is_function && is_file_local)
    {
      const code_typet &code_type=to_code_type(symbol.type);
      if(code_type.return_type().id()==ID_constructor ||
         code_type.return_type().id()==ID_destructor)
        is_file_local=false;
    }

    if(is_type)
    {
      // never EXPORTED by itself
    }
    else if(is_function)
    {
      // body? not local (i.e., "static")?
      if(has_body && !is_file_local)
        get_symbols_rec(ns, symbol, exported);
    }
    else
    {
      // 'extern' symbols are only exported if there
      // is an initializer.
      if((has_initializer || !symbol.is_extern) && 
         !is_file_local)
      {
        get_symbols_rec(ns, symbol, exported);
      }
    }
  }

  // remove all that are _not_ exported!
  for(symbol_tablet::symbolst::iterator
      it=symbol_table.symbols.begin();
      it!=symbol_table.symbols.end();
      ) // no it++
  {
    if(exported.find(it->first)==exported.end())
    {
      it=symbol_table.symbols.erase(it);
    }
    else
    {
      unused_files.erase(it->second.location.get_file());
      it++;
    }
  }

  unused_files.erase("gcc_builtin_headers_generic.h");
  unused_files.erase("gcc_builtin_headers_ia32.h");
  unused_files.erase("gcc_builtin_headers_ia32-2.h");
  unused_files.erase("gcc_builtin_headers_alpha.h");
  unused_files.erase("gcc_builtin_headers_arm.h");
  unused_files.erase("gcc_builtin_headers_mips.h");
  unused_files.erase("gcc_builtin_headers_power.h");
  unused_files.erase("arm_builtin_headers.h");
  unused_files.erase("cw_builtin_headers.h");
  unused_files.erase("clang_builtin_headers.h");

  // using deprecated message_streamt to set error location
  message_streamt message(message_handler);

  for(const std::pair<irep_idt, file_infot> &uf : unused_files)
  {
    message.err_location(uf.second.included_from);
    std::string msg=
      "warning: no declarations of #include "+
      id2string(uf.first)+" used";

    if(uf.second.is_system_header)
      msg+=" (system header)";

    if(!uf.second.is_nested)
      message.warning_msg(msg);
    else
      message.debug_msg(msg);
  }
}

