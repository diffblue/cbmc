/*******************************************************************\

Module:

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "format_hooks.h"

#include <util/format_expr.h>
#include <util/format_type.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>

#include "in_interval_expr.h"
#include "state.h"

void format_hooks()
{
  add_format_hook(
    ID_object_address,
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &object_address_expr = to_object_address_expr(expr);
      os << u8"\u275d" << object_address_expr.object_identifier() << u8"\u275e";
      return os;
    });

  add_format_hook(
    ID_object_size, [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &object_size_expr = to_object_size_expr(expr);
      os << "object_size(" << format(object_size_expr.op()) << ')';
      return os;
    });

  add_format_hook(
    ID_pointer_offset,
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &pointer_offset_expr = to_pointer_offset_expr(expr);
      os << "pointer_offset(" << format(pointer_offset_expr.op()) << ')';
      return os;
    });

  add_format_hook(
    ID_state_object_size,
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &object_size_expr = to_binary_expr(expr);
      os << "object_size(" << format(object_size_expr.op0()) << ", "
         << format(object_size_expr.op1()) << ')';
      return os;
    });

  add_format_hook(
    ID_field_address,
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &field_address_expr = to_field_address_expr(expr);
      os << format(field_address_expr.base()) << u8".\u275d"
         << field_address_expr.component_name() << u8"\u275e";
      return os;
    });

  add_format_hook(
    ID_evaluate, [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &evaluate_expr = to_evaluate_expr(expr);
      if(evaluate_expr.op0().id() == ID_symbol)
        os << format(evaluate_expr.op0());
      else
        os << '(' << format(evaluate_expr.op0()) << ')';
      os << '(' << format(evaluate_expr.op1()) << ')';
      return os;
    });

  add_format_hook(
    ID_update_state, [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &update_state_expr = to_update_state_expr(expr);
      os << format(update_state_expr.state()) << '['
         << format(update_state_expr.address())
         << ":=" << format(update_state_expr.new_value()) << ']';
      return os;
    });

  add_format_hook(
    ID_is_cstring, [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &is_cstring_expr = to_unary_expr(expr);
      return os << "is_cstring(" << format(is_cstring_expr.op()) << ')';
    });

  add_format_hook(
    ID_state_is_cstring,
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &is_cstring_expr = to_state_is_cstring_expr(expr);
      return os << "is_cstring(" << format(is_cstring_expr.state()) << ", "
                << format(is_cstring_expr.address()) << ')';
    });

  add_format_hook(
    ID_state_is_dynamic_object,
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &is_dynamic_object_expr =
        to_state_is_dynamic_object_expr(expr);
      return os << "is_dynamic_object("
                << format(is_dynamic_object_expr.state()) << ", "
                << format(is_dynamic_object_expr.address()) << ')';
    });

  add_format_hook(
    ID_state_r_ok, [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &r_ok_expr = to_ternary_expr(expr);
      return os << "r_ok(" << format(r_ok_expr.op0()) << ", "
                << format(r_ok_expr.op1()) << ", " << format(r_ok_expr.op2())
                << ')';
    });

  add_format_hook(
    ID_state_live_object,
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &live_object_expr = to_binary_expr(expr);
      return os << "live_object(" << format(live_object_expr.op0()) << ", "
                << format(live_object_expr.op1()) << ')';
    });

  add_format_hook(
    ID_state_writeable_object,
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &writeable_object_expr = to_binary_expr(expr);
      return os << "writeable_object(" << format(writeable_object_expr.op0())
                << ", " << format(writeable_object_expr.op1()) << ')';
    });

  add_format_hook(
    ID_state_type_compatible,
    [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &type_compatible_expr = to_state_type_compatible_expr(expr);
      return os << "type_compatible(" << format(type_compatible_expr.state())
                << ", " << format(type_compatible_expr.address()) << ')';
    });

  add_format_hook(
    ID_side_effect, [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &side_effect_expr = to_side_effect_expr(expr);
      if(side_effect_expr.get_statement() == ID_nondet)
        return os << "nondet " << format(side_effect_expr.type());
      else
        return os << "side-effect-" << side_effect_expr.get_statement();
    });

  add_format_hook(
    "in_interval", [](std::ostream &os, const exprt &expr) -> std::ostream & {
      const auto &in_interval_expr = to_in_interval_expr(expr);
      return os << format(in_interval_expr.value()) << " in ["
                << format(in_interval_expr.lower()) << ", "
                << format(in_interval_expr.upper()) << ']';
    });
}
