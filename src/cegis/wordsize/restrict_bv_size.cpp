/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <goto-programs/goto_functions.h>

#include <cegis/wordsize/restrict_bv_size.h>

void restrict_bv_size(symbol_tablet &st, goto_functionst &gf,
    const size_t width_in_bits)
{
  for(symbol_tablet::symbolst::value_type &id_and_symbol : st.symbols)
  {
    symbolt &symbol=id_and_symbol.second;
    restrict_bv_size(symbol.type, width_in_bits);
    restrict_bv_size(symbol.value, width_in_bits);
  }
  for(goto_functionst::function_mapt::value_type &entry : gf.function_map)
  {
    goto_functionst::function_mapt::value_type::second_type &func=entry.second;
    restrict_bv_size(func.type, width_in_bits);
    if(!func.body_available()) continue;
    goto_programt::instructionst &body=func.body.instructions;
    for(goto_programt::instructiont &instr : body)
    {
      restrict_bv_size(instr.code, width_in_bits);
      restrict_bv_size(instr.guard, width_in_bits);
    }
  }
}

namespace
{
bool is_bv_type(const typet &type)
{
  const irep_idt &type_id=type.id();
  return type_id == ID_signedbv || type_id == ID_unsignedbv
      || type_id == ID_fixedbv || type_id == ID_floatbv
      || type_id == ID_verilog_signedbv || type_id == ID_verilog_unsignedbv
      || type_id == ID_bv || type_id == ID_pointer || type_id == ID_c_bit_field
      || type_id == ID_c_bool;
}

class restrict_bv_size_visitort: public expr_visitort
{
  const size_t width_in_bits;
public:
  explicit restrict_bv_size_visitort(const size_t width_in_bits) :
      width_in_bits(width_in_bits)
  {
  }
  virtual ~restrict_bv_size_visitort()
  {
  }

  virtual void operator()(exprt &expr)
  {
    typet &type=expr.type();
    if(!restrict_bv_size(type, width_in_bits)) return;
    if(ID_constant != expr.id()) return;
    constant_exprt &constant=to_constant_expr(expr);
    const std::string &value=id2string(constant.get_value());
    if(value.empty()) return;
    assert(width_in_bits < value.size());
    std::string new_value(value.substr(value.size() - width_in_bits));
    // XXX: Restrict positive constant from being turned negative. Sensible?
    if(ID_signedbv == type.id()) new_value[0]=value[0];
    constant.set_value(new_value);
  }
};
}

void restrict_bv_size(exprt &expr, const size_t width_in_bits)
{
  restrict_bv_size_visitort visitor(width_in_bits);
  expr.visit(visitor);
}

namespace
{
bool restrict_bv_size(code_typet &type, const size_t width_in_bits)
{
  restrict_bv_size(type.return_type(), width_in_bits);
  for(code_typet::parametert &param : type.parameters())
  {
    restrict_bv_size(param, width_in_bits);
    restrict_bv_size(param.default_value(), width_in_bits);
  }
  return false;
}

bool restrict_bv_size(struct_union_typet &type, const size_t width_in_bits)
{
  for(struct_union_typet::componentt &comp : type.components())
    restrict_bv_size(comp, width_in_bits);
  return false;
}
}

bool restrict_bv_size(typet &type, const size_t width_in_bits)
{
  const irep_idt &type_id=type.id();
  if(ID_code == type_id)
    return restrict_bv_size(to_code_type(type), width_in_bits);
  if(ID_struct == type_id || ID_union == type_id)
    return restrict_bv_size(to_struct_union_type(type), width_in_bits);
  if(static_cast<const typet &>(type).subtype().is_not_nil())
    restrict_bv_size(type.subtype(), width_in_bits);
  if(!is_bv_type(type)) return false;
  bitvector_typet &bvtype=to_bitvector_type(type);
  if(width_in_bits >= bvtype.get_width()) return false;
  to_bitvector_type(type).set_width(width_in_bits);
  return true;
}
