/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cstring>
#include <algorithm>
#include <iterator>

#include <cegis/instructions/instruction_set_factory.h>
#include <cegis/genetic/instruction_set_info_factory.h>

instruction_set_info_factoryt::instruction_set_info_factoryt(
    const goto_programt &body) :
    body_provider([&body] () -> const goto_programt &
    { return body;})
{
}

instruction_set_info_factoryt::~instruction_set_info_factoryt()
{
}

namespace
{
const char OPCODE_SIGNIFIER[]="::opcode";
const char OP_SIGNIFIER[]="::op";

class count_ops: public const_expr_visitort
{
  size_t count;
public:
  count_ops() :
      count(0u)
  {
  }

  virtual ~count_ops()
  {
  }

  virtual void operator()(const exprt &expr)
  {
    if(ID_symbol != expr.id()) return;
    const std::string &id=id2string(to_symbol_expr(expr).get_identifier());
    if(std::string::npos != id.find(OPCODE_SIGNIFIER)) return;
    const std::string::size_type op_id_pos=id.find(OP_SIGNIFIER);
    if(std::string::npos == op_id_pos) return;
    const std::string::size_type value_pos=op_id_pos + strlen(OP_SIGNIFIER);
    const mp_integer::llong_t v=string2integer(id.substr(value_pos)).to_long();
    const size_t op_id=static_cast<size_t>(v);
    count=std::max(count, op_id + 1);
  }

  void operator()(const goto_programt::instructiont &instr)
  {
    instr.guard.visit(*this);
    instr.code.visit(*this);
  }

  const count_ops &operator()(const goto_programt::instructionst &instrs)
  {
    for(const goto_programt::instructiont &instr : instrs)
      this->operator()(instr);
    return *this;
  }

  size_t get_count() const
  {
    return count;
  }
};

class transform_to_info
{
public:
  transform_to_info()
  {
  }

  instruction_set_infot::value_type operator()(
      const instruction_sett::value_type &instr) const
  {
    const size_t count=count_ops()(instr.second).get_count();
    return std::make_pair(instr.first, count);
  }
};

void initialise(instruction_set_infot &info, instruction_sett &ins,
    const std::function<const goto_programt&(void)> &body_provider)
{
  if(!info.empty()) return;
  const goto_programt &body=body_provider();
  ins=extract_instruction_set(body);
  const transform_to_info op;
  std::transform(ins.begin(), ins.end(), std::inserter(info, info.end()), op);
}
}

const instruction_sett &instruction_set_info_factoryt::get_instructions()
{
  initialise(info, instructions, body_provider);
  return instructions;
}

const instruction_set_infot &instruction_set_info_factoryt::get_info()
{
  initialise(info, instructions, body_provider);
  return info;
}
