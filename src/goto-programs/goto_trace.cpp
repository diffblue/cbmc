/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

  Date: July 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

#include "goto_trace.h"

#include <cassert>
#include <ostream>

#include <util/arith_tools.h>
#include <util/symbol.h>

#include <ansi-c/printf_formatter.h>
#include <langapi/language_util.h>

void goto_tracet::output(
  const class namespacet &ns,
  std::ostream &out) const
{
  for(const auto &step : steps)
    step->output(ns, out);
}

void goto_trace_stept::output(
  const namespacet &ns,
  std::ostream &out) const
{
  out << "*** " << name() << formatted_cond_value() << (hidden ? " hidden" : "")
      << '\n';

  if(!pc->source_location.is_nil())
    out << pc->source_location << "\n";

  if(pc->is_goto())
    out << "GOTO   ";
  else if(pc->is_assume())
    out << "ASSUME ";
  else if(pc->is_assert())
    out << "ASSERT ";
  else if(pc->is_dead())
    out << "DEAD   ";
  else if(pc->is_other())
    out << "OTHER  ";
  else if(pc->is_assign())
    out << "ASSIGN ";
  else if(pc->is_decl())
    out << "DECL   ";
  else if(pc->is_function_call())
    out << "CALL   ";
  else
    out << "(?)    ";

  out << "\n";

  if((pc->is_other() && lhs_object.is_not_nil()) || pc->is_assign())
  {
    irep_idt identifier=lhs_object.get_object_name();
    out << "  " << from_expr(ns, identifier, lhs_object.get_original_expr())
        << " = " << from_expr(ns, identifier, lhs_object_value)
        << "\n";
  }
  else if(pc->is_assert())
  {
    if(!cond_value)
    {
      out << "Violated property:" << "\n";
      if(pc->source_location.is_nil())
        out << "  " << pc->source_location << "\n";

      if(comment!="")
        out << "  " << comment << "\n";
      out << "  " << from_expr(ns, "", pc->guard) << "\n";
      out << "\n";
    }
  }

  out << "\n";
}

std::string trace_value_binary(
  const exprt &expr,
  const namespacet &ns)
{
  const typet &type=ns.follow(expr.type());

  if(expr.id()==ID_constant)
  {
    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_bv ||
       type.id()==ID_fixedbv ||
       type.id()==ID_floatbv ||
       type.id()==ID_pointer ||
       type.id()==ID_c_bit_field ||
       type.id()==ID_c_bool ||
       type.id()==ID_c_enum ||
       type.id()==ID_c_enum_tag)
    {
      return expr.get_string(ID_value);
    }
    else if(type.id()==ID_bool)
    {
      return expr.is_true()?"1":"0";
    }
  }
  else if(expr.id()==ID_array)
  {
    std::string result;

    forall_operands(it, expr)
    {
      if(result=="")
        result="{ ";
      else
        result+=", ";
      result+=trace_value_binary(*it, ns);
    }

    return result+" }";
  }
  else if(expr.id()==ID_struct)
  {
    std::string result="{ ";

    forall_operands(it, expr)
    {
      if(it!=expr.operands().begin())
        result+=", ";
      result+=trace_value_binary(*it, ns);
    }

    return result+" }";
  }
  else if(expr.id()==ID_union)
  {
    assert(expr.operands().size()==1);
    return trace_value_binary(expr.op0(), ns);
  }

  return "?";
}

void trace_value(
  std::ostream &out,
  const namespacet &ns,
  const ssa_exprt &lhs_object,
  const exprt &full_lhs,
  const exprt &value)
{
  irep_idt identifier;

  if(lhs_object.is_not_nil())
    identifier=lhs_object.get_object_name();

  std::string value_string;

  if(value.is_nil())
    value_string="(assignment removed)";
  else
  {
    value_string=from_expr(ns, identifier, value);

    // the binary representation
    value_string+=" ("+trace_value_binary(value, ns)+")";
  }

  out << "  "
      << from_expr(ns, identifier, full_lhs)
      << "=" << value_string
      << "\n";
}

void show_state_header(
  std::ostream &out,
  const goto_trace_stept &state,
  const source_locationt &source_location,
  unsigned step_nr)
{
  out << "\n";

  if(step_nr==0)
    out << "Initial State";
  else
    out << "State " << step_nr;

  out << " " << source_location
      << " thread " << state.thread_nr << "\n";
  out << "----------------------------------------------------" << "\n";
}

bool is_index_member_symbol(const exprt &src)
{
  if(src.id()==ID_index)
    return is_index_member_symbol(src.op0());
  else if(src.id()==ID_member)
    return is_index_member_symbol(src.op0());
  else if(src.id()==ID_symbol)
    return true;
  else
    return false;
}

namespace
{
class show_goto_trace_visitort final : public trace_const_visitor_const_argst
{
public:
  show_goto_trace_visitort(
    std::ostream &out,
    const namespacet &ns,
    unsigned &prev_step_nr,
    bool &first_step)
    : out_{out}, ns_{ns}, prev_step_nr_{prev_step_nr}, first_step_{first_step}
  {
  }

  void visit(const trace_assignmentt &x) const override
  {
    if(
      x.pc->is_assign() || x.pc->is_return() || // returns have a lhs!
      x.pc->is_function_call() ||
      (x.pc->is_other() && x.lhs_object.is_not_nil()))
    {
      if(prev_step_nr_ != x.step_nr || first_step_)
      {
        first_step_ = false;
        prev_step_nr_ = x.step_nr;
        show_state_header(out_, x, x.pc->source_location, x.step_nr);
      }

      // see if the full lhs is something clean
      if(is_index_member_symbol(x.full_lhs))
        trace_value(out_, ns_, x.lhs_object, x.full_lhs, x.full_lhs_value);
      else
        trace_value(out_, ns_, x.lhs_object, x.lhs_object, x.lhs_object_value);
    }
  }

  void visit(const trace_assumet &x) const override
  {
    if(!x.cond_value)
    {
      out_ << "\n";
      out_ << "Violated assumption:"
           << "\n";
      if(!x.pc->source_location.is_nil())
        out_ << "  " << x.pc->source_location << "\n";

      if(x.pc->is_assume())
        out_ << "  " << from_expr(ns_, "", x.pc->guard) << "\n";

      out_ << "\n";
    }
  }

  void visit(const trace_assertt &x) const override
  {
    if(!x.cond_value)
    {
      out_ << "\n";
      out_ << "Violated property:"
          << "\n";
      if(!x.pc->source_location.is_nil())
        out_ << "  " << x.pc->source_location << "\n";
      out_ << "  " << x.comment << "\n";

      if(x.pc->is_assert())
        out_ << "  " << from_expr(ns_, "", x.pc->guard) << "\n";

      out_ << "\n";
    }
  }

  void visit(const trace_gotot &x) const override
  {
  }

  void visit(const trace_locationt &x) const override
  {
  }

  void visit(const trace_inputt &x) const override
  {
    show_state_header(out_, x, x.pc->source_location, x.step_nr);
    out_ << "  INPUT " << x.io_id << ":";

    for(auto l_it = x.io_args.begin(); l_it != x.io_args.end(); ++l_it)
    {
      if(l_it != x.io_args.begin())
        out_ << ";";
      out_ << " " << from_expr(ns_, "", *l_it);

      // the binary representation
      out_ << " (" << trace_value_binary(*l_it, ns_) << ")";
    }

    out_ << "\n";
  }

  void visit(const trace_outputt &x) const override
  {
    if(x.formatted)
    {
      printf_formattert printf_formatter(ns_);
      printf_formatter(id2string(x.format_string), x.io_args);
      printf_formatter.print(out_);
      out_ << "\n";
    }
    else
    {
      show_state_header(out_, x, x.pc->source_location, x.step_nr);
      out_ << "  OUTPUT " << x.io_id << ":";

      for(auto l_it = x.io_args.begin(); l_it != x.io_args.end(); ++l_it)
      {
        if(l_it != x.io_args.begin())
          out_ << ";";
        out_ << " " << from_expr(ns_, "", *l_it);

        // the binary representation
        out_ << " (" << trace_value_binary(*l_it, ns_) << ")";
      }

      out_ << '\n';
    }
  }

  void visit(const trace_declt &x) const override
  {
    if(prev_step_nr_ != x.step_nr || first_step_)
    {
      first_step_ = false;
      prev_step_nr_ = x.step_nr;
      show_state_header(out_, x, x.pc->source_location, x.step_nr);
    }

    trace_value(out_, ns_, x.lhs_object, x.full_lhs, x.full_lhs_value);
  }

  void visit(const trace_deadt &x) const override
  {
  }

  void visit(const trace_function_callt &x) const override
  {
  }

  void visit(const trace_function_returnt &x) const override
  {
  }

  void visit(const trace_constraintt &x) const override
  {
    UNREACHABLE;
  }

  void visit(const trace_shared_readt &x) const override
  {
    UNREACHABLE;
  }

  void visit(const trace_shared_writet &x) const override
  {
    UNREACHABLE;
  }

  void visit(const trace_spawnt &x) const override
  {
  }

  void visit(const trace_memory_barriert &x) const override
  {
  }

  void visit(const trace_atomic_begint &x) const override
  {
  }

  void visit(const trace_atomic_endt &x) const override
  {
  }

private:
  std::ostream &out_;
  const namespacet &ns_;
  unsigned &prev_step_nr_;
  bool &first_step_;
};

} // namespace

void show_goto_trace(
  std::ostream &out,
  const namespacet &ns,
  const goto_tracet &goto_trace)
{
  unsigned prev_step_nr=0;
  bool first_step=true;

  for(const auto &step : goto_trace.steps)
  {
    // hide the hidden ones
    if(step->hidden)
      continue;

    step->accept(show_goto_trace_visitort{out, ns, prev_step_nr, first_step});
  }
}

bool goto_trace_stept::is_assignment() const
{ return dynamic_cast<const trace_assignmentt*>(this) != nullptr; }
bool goto_trace_stept::is_assume() const
{ return dynamic_cast<const trace_assumet*>(this)!=nullptr; }
bool goto_trace_stept::is_assert() const
{ return dynamic_cast<const trace_assertt*>(this)!=nullptr; }
bool goto_trace_stept::is_goto() const
{ return dynamic_cast<const trace_gotot*>(this)!=nullptr; }
bool goto_trace_stept::is_constraint() const
{ return dynamic_cast<const trace_constraintt*>(this)!=nullptr; }
bool goto_trace_stept::is_function_call() const
{ return dynamic_cast<const trace_function_callt*>(this)!=nullptr; }
bool goto_trace_stept::is_function_return() const
{ return dynamic_cast<const trace_function_returnt*>(this)!=nullptr; }
bool goto_trace_stept::is_location() const
{ return dynamic_cast<const trace_locationt*>(this)!=nullptr; }
bool goto_trace_stept::is_output() const
{ return dynamic_cast<const trace_outputt*>(this)!=nullptr; }
bool goto_trace_stept::is_input() const
{ return dynamic_cast<const trace_inputt*>(this)!=nullptr; }
bool goto_trace_stept::is_decl() const
{ return dynamic_cast<const trace_declt*>(this)!=nullptr; }
bool goto_trace_stept::is_dead() const
{ return dynamic_cast<const trace_deadt*>(this)!=nullptr; }
bool goto_trace_stept::is_shared_read() const
{ return dynamic_cast<const trace_shared_readt*>(this)!=nullptr; }
bool goto_trace_stept::is_shared_write() const
{ return dynamic_cast<const trace_shared_writet*>(this)!=nullptr; }
bool goto_trace_stept::is_spawn() const
{ return dynamic_cast<const trace_spawnt*>(this)!=nullptr; }
bool goto_trace_stept::is_memory_barrier() const
{ return dynamic_cast<const trace_memory_barriert*>(this)!=nullptr; }
bool goto_trace_stept::is_atomic_begin() const
{ return dynamic_cast<const trace_atomic_begint*>(this)!=nullptr; }
bool goto_trace_stept::is_atomic_end() const
{ return dynamic_cast<const trace_atomic_endt*>(this)!=nullptr; }
