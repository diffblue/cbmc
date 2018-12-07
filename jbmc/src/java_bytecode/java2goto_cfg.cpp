/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java2goto.h"

#include "pattern.h"

#include <util/arith_tools.h>

goto_programt convert_cfg(const java_bytecode_parse_treet::methodt &method)
{
  goto_programt dest;
  std::map<std::size_t, goto_programt::targett> target_map;

  for(const auto &instruction : method.instructions)
  {
    auto t = dest.add_instruction();
    target_map[instruction.address] = t;
    codet c(instruction.statement);
    c.operands() = instruction.args;
    t->make_other(c);
    t->source_location = instruction.source_location;
  }

  auto end_function = dest.add_instruction();
  end_function->make_end_function();

  // resolve goto targets
  for(auto &instruction : dest.instructions)
  {
    const auto &statement = instruction.code.get_statement();
    if(statement == "goto")
    {
      DATA_INVARIANT(instruction.code.operands().size() == 1, "goto operand");
      auto target_address =
        numeric_cast_v<std::size_t>(to_constant_expr(instruction.code.op0()));
      const auto t_it = target_map.find(target_address);
      if(t_it == target_map.end())
        throw "goto target not found";
      instruction.set_target(t_it->second);
    }
    else if(statement == "return" || patternt("?return") == statement)
    {
      instruction.set_target(end_function);
    }
  }

  dest.update();

  return dest;
}
