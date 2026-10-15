/*******************************************************************\

Module: State Encoding Targets

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "state_encoding_targets.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/exception_utils.h>
#include <util/format_expr.h>
#include <util/pointer_offset_size.h>

#include <ostream>

void ascii_encoding_targett::set_to_true(source_locationt, exprt expr)
{
  counter++;
  if(counter < 10)
    out << ' ';
  out << '(' << counter << ')' << ' ';
  out << format(expr) << '\n';
}

void state_encoding_smt2_convt::add_converters()
{
#if 0
  auto make_unary = [this](const char *f) {
    return [this, f](const exprt &expr) {
      const auto &unary_expr = to_unary_expr(expr);
      out << '(' << f << ' ';
      convert_expr(unary_expr.op());
      out << ')';
    };
  };
#endif

  auto make_binary = [this](const char *f) {
    return [this, f](const exprt &expr) {
      const auto &binary_expr = to_binary_expr(expr);
      out << '(' << f << ' ';
      convert_expr(binary_expr.op0());
      out << ' ';
      convert_expr(binary_expr.op1());
      out << ')';
    };
  };

  auto make_ternary = [this](const char *f) {
    return [this, f](const exprt &expr) {
      const auto &ternary_expr = to_ternary_expr(expr);
      out << '(' << f << ' ';
      convert_expr(ternary_expr.op0());
      out << ' ';
      convert_expr(ternary_expr.op1());
      out << ' ';
      convert_expr(ternary_expr.op2());
      out << ')';
    };
  };

  set_converter(ID_update_state, [this](const exprt &expr) {
    out << "(update-state-" << type2id(to_ternary_expr(expr).op2().type())
        << ' ';
    convert_expr(to_ternary_expr(expr).op0());
    out << ' ';
    convert_expr(to_ternary_expr(expr).op1());
    out << ' ';
    convert_expr(to_ternary_expr(expr).op2());
    out << ')';
  });

  set_converter(ID_enter_scope_state, [this](const exprt &expr) {
    out << "(enter-scope-state-" << type2id(to_binary_expr(expr).op1().type())
        << ' ';
    convert_expr(to_binary_expr(expr).op0());
    out << ' ';
    convert_expr(to_binary_expr(expr).op1());
    out << ' ';
    const auto &base_type =
      to_pointer_type(to_binary_expr(expr).op1().type()).base_type();
    auto size_opt = size_of_expr(base_type, ns);
    if(size_opt.has_value())
      convert_expr(*size_opt);
    else if(
      base_type.id() == ID_integer || base_type.id() == ID_natural ||
      base_type.id() == ID_rational || base_type.id() == ID_real)
    {
      // Mathematical types (as used by the Strata encoding) have no byte
      // size. Such objects are not byte-addressed, so the enter-scope size is
      // immaterial and a unit size is sound. Any other type without a size is
      // unexpected (e.g. a function or incomplete type) and fails loudly
      // below.
      convert_expr(from_integer(1, size_type()));
    }
    else
      throw incorrect_goto_program_exceptiont(
        "enter-scope-state for an object whose type has no byte size: " +
        base_type.id_string());
    out << ')';
  });

  set_converter(ID_exit_scope_state, [this](const exprt &expr) {
    out << "(exit-scope-state-" << type2id(to_binary_expr(expr).op1().type())
        << ' ';
    convert_expr(to_binary_expr(expr).op0());
    out << ' ';
    convert_expr(to_binary_expr(expr).op1());
    out << ')';
  });

  set_converter(ID_allocate, [this](const exprt &expr) {
    out << "(allocate ";
    convert_expr(to_binary_expr(expr).op0());
    out << ' ';
    convert_expr(to_binary_expr(expr).op1());
    out << ')';
  });

  set_converter(ID_allocate_state, [this](const exprt &expr) {
    out << "(allocate ";
    convert_expr(to_binary_expr(expr).op0());
    out << ' ';
    convert_expr(to_binary_expr(expr).op1());
    out << ')';
  });

  set_converter(ID_reallocate, [this](const exprt &expr) {
    out << "(reallocate ";
    convert_expr(to_ternary_expr(expr).op0());
    out << ' ';
    convert_expr(to_ternary_expr(expr).op1());
    out << ' ';
    convert_expr(to_ternary_expr(expr).op2());
    out << ')';
  });

  set_converter(ID_deallocate_state, [this](const exprt &expr) {
    out << "(deallocate ";
    convert_expr(to_binary_expr(expr).op0());
    out << ' ';
    convert_expr(to_binary_expr(expr).op1());
    out << ')';
  });

  set_converter(ID_evaluate, [this](const exprt &expr) {
    out << "(evaluate-" << type2id(expr.type()) << ' ';
    convert_expr(to_binary_expr(expr).op0());
    out << ' ';
    convert_expr(to_binary_expr(expr).op1());
    out << ')';
  });

  set_converter(ID_state_is_cstring, make_binary("state-is-cstring"));

  set_converter(ID_initial_state, [this](const exprt &expr) { out << "true"; });

  set_converter(
    ID_state_is_dynamic_object, make_binary("state-is-dynamic-object"));

  set_converter(ID_state_live_object, make_binary("state-live-object"));

  set_converter(
    ID_state_writeable_object, make_binary("state-writeable-object"));

  set_converter(ID_state_is_sentinel_dll, [this](const exprt &expr) {
    if(expr.operands().size() == 3)
    {
      out << "(state-is-sentinel-dll ";
      convert_expr(to_multi_ary_expr(expr).op0());
      out << ' ';
      convert_expr(to_multi_ary_expr(expr).op1());
      out << ' ';
      convert_expr(to_multi_ary_expr(expr).op2());
      out << ')';
    }
    else
    {
      out << "(state-is-sentinel-dll-with-node ";
      convert_expr(to_multi_ary_expr(expr).op0());
      out << ' ';
      convert_expr(to_multi_ary_expr(expr).op1());
      out << ' ';
      convert_expr(to_multi_ary_expr(expr).op2());
      out << ' ';
      convert_expr(to_multi_ary_expr(expr).op3());
      out << ')';
    }
  });

  set_converter(ID_state_live_object, make_binary("state-live-object"));

  set_converter(
    ID_state_writeable_object, make_binary("state-writeable-object"));

  set_converter(ID_state_r_ok, make_ternary("state-r-ok"));

  set_converter(ID_state_w_ok, make_ternary("state-w-ok"));

  set_converter(ID_state_rw_ok, make_ternary("state-rw-ok"));
}
