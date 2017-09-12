/*******************************************************************\

Module: Unwind loops in static initializers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Unwind loops in static initializers

#include "remove_static_init_loops.h"

#include <algorithm>

#include <util/suffix.h>
#include <util/string2int.h>

class remove_static_init_loopst
{
public:
  explicit remove_static_init_loopst(
    const symbol_tablet &_symbol_table):
    symbol_table(_symbol_table)
    {}

  void unwind_enum_static(
    const goto_functionst &goto_functions,
    optionst &options,
    message_handlert &);
protected:
  const symbol_tablet &symbol_table;
};

/// unwind static initialization loops of Java enums as far as the enum has
/// elements, thus flattening them completely
/// \par parameters: goto_functions and options
/// \return side effect is adding <clinit> loops to unwindset
void remove_static_init_loopst::unwind_enum_static(
  const goto_functionst &goto_functions,
  optionst &options,
  message_handlert &msg)
{
  size_t unwind_max=0;
  messaget message;
  message.set_message_handler(msg);
  forall_goto_functions(f, goto_functions)
  {
    auto &p=f->second.body;
    for(const auto &ins : p.instructions)
    {
      // is this a loop?
      if(ins.is_backwards_goto())
      {
        size_t loop_id=ins.loop_number;
        const std::string java_clinit="<clinit>:()V";
        const std::string &fname=id2string(ins.function);
        size_t class_prefix_length=fname.find_last_of('.');
        // is the function symbol in the symbol table?
        if(!symbol_table.has_symbol(ins.function))
        {
          message.warning() << "function `" << id2string(ins.function)
                            << "` is not in symbol table" << messaget::eom;
          continue;
        }
        // is Java function and static init?
        const symbolt &function_name=symbol_table.lookup(ins.function);
        if(!(function_name.mode==ID_java && has_suffix(fname, java_clinit)))
          continue;
        assert(
          class_prefix_length!=std::string::npos &&
          "could not identify class name");
        const std::string &classname=fname.substr(0, class_prefix_length);
        const symbolt &class_symbol=symbol_table.lookup(classname);
        const class_typet &class_type=to_class_type(class_symbol.type);
        size_t unwinds=class_type.get_size_t(ID_java_enum_static_unwind);

        unwind_max=std::max(unwind_max, unwinds);
        if(unwinds>0)
        {
          const std::string &set=options.get_option("unwindset");
          std::string newset;
          if(set!="")
            newset=",";
          newset+=
            id2string(ins.function)+"."+std::to_string(loop_id)+":"+
            std::to_string(unwinds);
          options.set_option("unwindset", set+newset);
        }
      }
    }
  }
  const std::string &vla_length=options.get_option("java-max-vla-length");
  if(!vla_length.empty())
  {
    size_t max_vla_length=safe_string2unsigned(vla_length);
    if(max_vla_length<unwind_max)
      throw "cannot unwind <clinit> due to insufficient max vla length";
  }
}

/// this is the entry point for the removal of loops in static initialization
/// code of Java enums
/// \par parameters: symbol table, goto_functions and options
/// \return side effect is adding <clinit> loops to unwindset
void remove_static_init_loops(
  const symbol_tablet &symbol_table,
  const goto_functionst &goto_functions,
  optionst &options,
  message_handlert &msg)
{
  remove_static_init_loopst remove_loops(symbol_table);
  remove_loops.unwind_enum_static(goto_functions, options, msg);
}
