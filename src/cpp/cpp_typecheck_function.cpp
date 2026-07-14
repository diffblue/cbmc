/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include "cpp_convert_type.h"
#include "cpp_name.h"
#include "cpp_sfinae_context.h"
#include "cpp_template_type.h"
#include "cpp_type2name.h"
#include "cpp_typecheck.h"

#include <functional>
#include <optional>
#include <set>

void cpp_typecheckt::convert_parameter(
  const irep_idt &current_mode,
  code_typet::parametert &parameter)
{
  irep_idt base_name=id2string(parameter.get_base_name());

  if(base_name.empty())
  {
    base_name="#anon_arg"+std::to_string(anon_counter++);
    parameter.set_base_name(base_name);
  }

  PRECONDITION(!cpp_scopes.current_scope().prefix.empty());
  irep_idt identifier=cpp_scopes.current_scope().prefix+
                      id2string(base_name);

  parameter.set_identifier(identifier);

  // the parameter may already have been set up if dealing with virtual methods
  const symbolt *check_symbol;
  if(!lookup(identifier, check_symbol))
    return;

  parameter_symbolt symbol;

  symbol.name=identifier;
  symbol.base_name=parameter.get_base_name();
  symbol.location=parameter.source_location();
  symbol.mode = current_mode;
  symbol.module=module;
  symbol.type=parameter.type();
  symbol.is_lvalue=!is_reference(symbol.type);

  INVARIANT(!symbol.base_name.empty(), "parameter has base name");

  symbolt *new_symbol;

  if(symbol_table.move(symbol, new_symbol))
  {
    error().source_location=symbol.location;
    error() << "cpp_typecheckt::convert_parameter: symbol_table.move(\""
            << symbol.name << "\") failed" << eom;
    throw 0;
  }

  // put into scope
  cpp_scopes.put_into_scope(*new_symbol);
}

void cpp_typecheckt::convert_parameters(
  const irep_idt &current_mode,
  code_typet &function_type)
{
  code_typet::parameterst &parameters=
    function_type.parameters();

  for(code_typet::parameterst::iterator
      it=parameters.begin();
      it!=parameters.end();
      it++)
    convert_parameter(current_mode, *it);
}

void cpp_typecheckt::convert_function(symbolt &symbol)
{
  // Guard against recursive type-checking (e.g., constexpr functions
  // that call themselves).
  if(functions_being_typechecked.count(symbol.name))
    return;
  functions_being_typechecked.insert(symbol.name);

  // A function body is a run-time context: suspend any enclosing
  // constant-expression context so its statements are not folded.
  non_constant_expression_contextt non_constant_guard{*this};

  code_typet &function_type=
    to_code_type(template_subtype(symbol.type));

  // only a prototype?
  if(symbol.value.is_nil())
    return;

  if(symbol.value.id() != ID_code)
  {
    error().source_location = symbol.location;
    error() << "function '" << symbol.name << "' is initialized with "
            << symbol.value.id() << eom;
    throw 0;
  }

  // C++11 deleted functions: = delete
  if(to_code(symbol.value).get_statement() == ID_cpp_delete)
  {
    symbol.value.make_nil();
    return;
  }

  // N5008 [temp.variadic]/5 + [dcl.spec.auto]/11: a function-template instance
  // whose body contains a call-argument pack expansion over a NON-type
  // parameter pack (e.g. `return add(I...)`) is normally expanded during the
  // deferred method-body drain (which runs expand_call_argument_packs).  A
  // function with a DEDUCED return type (`auto` / `decltype(auto)`) is instead
  // type-checked EAGERLY here, so its return type is known at the call site;
  // that path bypasses the drain, so without expanding the pack call first both
  // the return-type deduction and the body type-check below fail on the
  // unexpanded `add(I...)` (leaving the instance's return type unresolved, so
  // the call "finds no match").  Expand it now using this instance's deduced
  // pack values.  Gated on both a deduced return type and a non-type pack being
  // present (pack_expr_map), so the working deferred path and bodies with only
  // type / function-parameter packs are untouched; the expansion is idempotent
  // (an already-expanded call carries no `...`), so a later drain is a no-op.
  //
  // only_nontype: this eager conversion may run while an ENCLOSING
  // instantiation's template_map is still active (a nested deduced-return
  // callee -- e.g. std::apply's __apply_impl deducing its return type from
  // std::__invoke(...), which is itself instantiated here).  A function-
  // parameter pack in THIS body was already expanded at instantiation time, so
  // only the non-type call-argument pack must be expanded; expanding a value /
  // function-parameter pack against the enclosing map's unrelated pack size
  // would corrupt an already-expanded call (`add(a$0, a$1)` -> `add(a$0,
  // a$0)`).
  if(has_auto(symbol.type) && !template_map.pack_expr_map.empty())
    template_map.expand_call_argument_packs(
      static_cast<irept &>(symbol.value), /*only_nontype=*/true);

  // enter appropriate scope
  cpp_save_scopet saved_scope(cpp_scopes);
  cpp_scopet &function_scope=cpp_scopes.set_scope(symbol.name);

  // fix the scope's prefix
  function_scope.prefix=id2string(symbol.name)+"::";

  // For friend functions defined inside a class, add the class scope
  // as a secondary scope so that class-scope names are visible.
  // Also disable access control since friend functions can access
  // private/protected members of the befriending class.
  const irep_idt &friend_class = symbol.type.get(ID_C_class);
  bool saved_access_control = disable_access_control;
  if(!friend_class.empty())
  {
    auto it = cpp_scopes.id_map.find(friend_class);
    if(it != cpp_scopes.id_map.end())
      function_scope.add_secondary_scope(
        static_cast<cpp_scopet &>(*it->second));
    disable_access_control = true;
  }

  // genuine function definition -- do the parameter declarations
  convert_parameters(symbol.mode, function_type);

  // create "this" if it's a non-static method
  if(function_scope.is_method &&
     !function_scope.is_static_member)
  {
    code_typet::parameterst &parameters=function_type.parameters();
    DATA_INVARIANT(parameters.size() >= 1, "parameters expected");
    code_typet::parametert &this_parameter_expr=parameters.front();
    function_scope.this_expr = symbol_exprt{
      this_parameter_expr.get_identifier(), this_parameter_expr.type()};
  }
  else
    function_scope.this_expr.make_nil();

  // if it is a destructor, add the implicit code
  if(to_code_type(symbol.type).return_type().id() == ID_destructor)
  {
    const symbolt &msymb = lookup(symbol.type.get(ID_C_member_name));

    // Under normal operation a destructor body arrives here as a
    // code_blockt.  However, under error-recovery conditions (for
    // example after a prior CONVERSION ERROR has produced a
    // partially-elaborated class) we may see a destructor symbol
    // whose value is nil or not a block.  Skip the implicit-code
    // insertion in that case rather than aborting via a
    // PRECONDITION violation.
    if(
      symbol.value.id() != ID_code ||
      symbol.value.get(ID_statement) != ID_block)
    {
      return;
    }

    // Skip adding destructor code for virtual function thunks — the
    // thunk just calls the real destructor which already has the code.
    const auto &this_param_type =
      to_pointer_type(function_type.parameters().front().type());
    bool is_thunk =
      this_param_type.base_type().get(ID_identifier) != msymb.name;

    if(
      !is_thunk &&
      (!symbol.value.has_operands() ||
       !to_multi_ary_expr(symbol.value).op0().has_operands() ||
       to_multi_ary_expr(to_multi_ary_expr(symbol.value).op0()).op0().id() !=
         ID_already_typechecked))
    {
      symbol.value.copy_to_operands(
        dtor(msymb, to_symbol_expr(function_scope.this_expr)));
    }
  }

  // do the function body
  // Save and restore the return type and loop-context flags
  // exception-safely.  convert_function may be called recursively (e.g. a
  // template instantiation triggered while type-checking an expression in
  // another function body).  If such a nested call throws and is caught
  // upstream, a non-exception-safe restore would leave `return_type` set to
  // the nested function's return type; the enclosing function's subsequent
  // `return` statements would then be converted against the wrong type
  // (N5008 [stmt.return]/3 requires the operand to be implicitly converted
  // to the *enclosing* function's return type).  That produces a
  // type-inconsistent assignment that later trips the symbolic-execution
  // invariant lhs.type() == rhs.type().  A scope guard restores the saved
  // values on every exit -- normal return, early return, or exception.
  struct context_restoret
  {
    typet &return_type_ref;
    bool &break_ref;
    bool &continue_ref;
    bool &case_ref;
    const typet saved_return_type;
    const bool saved_break;
    const bool saved_continue;
    const bool saved_case;
    ~context_restoret()
    {
      return_type_ref = saved_return_type;
      break_ref = saved_break;
      continue_ref = saved_continue;
      case_ref = saved_case;
    }
  } context_restore{
    return_type,
    break_is_allowed,
    continue_is_allowed,
    case_is_allowed,
    return_type,
    break_is_allowed,
    continue_is_allowed,
    case_is_allowed};

  start_typecheck_code();

  return_type = function_type.return_type();

  // constructor, destructor?
  if(return_type.id() == ID_constructor || return_type.id() == ID_destructor)
    return_type = void_type();

  // C++14: auto return type deduction
  bool defer_auto_return = false;
  if(has_auto(return_type))
  {
    // Find the first return statement and deduce the type.
    // If the body contains if constexpr, the return expression may be
    // in a discarded branch and fail to type-check. In that case,
    // defer deduction to after body type-checking.
    std::function<const exprt *(const codet &)> find_return =
      [&](const codet &code) -> const exprt *
    {
      if(code.get_statement() == ID_return)
      {
        const auto &ret = to_code_frontend_return(code);
        if(ret.has_return_value())
          return &ret.return_value();
      }
      for(const auto &op : code.operands())
      {
        if(op.id() == ID_code)
        {
          const exprt *r = find_return(to_code(op));
          if(r != nullptr)
            return r;
        }
      }
      return nullptr;
    };

    const exprt *ret_expr = find_return(to_code(symbol.value));
    if(ret_expr != nullptr)
    {
      const std::size_t saved_errors =
        get_message_handler().get_message_count(messaget::M_ERROR);
      const unsigned saved_verbosity = get_message_handler().get_verbosity();
      get_message_handler().set_verbosity(0);

      try
      {
        exprt tmp = *ret_expr;
        typecheck_expr(tmp);
        typet deduced = tmp.type();
        // C++14 decltype(auto): if the return expression is a
        // parenthesized lvalue, deduce a reference type
        if(
          return_type.id() == ID_decltype && return_type.get_bool("#auto") &&
          tmp.get_bool(ID_C_lvalue))
        {
          deduced = reference_typet(deduced, config.ansi_c.pointer_width);
        }
        cpp_convert_auto(
          function_type.return_type(), deduced, get_message_handler());
        typecheck_type(function_type.return_type());
        return_type = function_type.return_type();
      }
      catch(...)
      {
        // Return expression failed to type-check (likely in a discarded
        // if constexpr branch). Defer deduction to after body type-checking.
        get_message_handler().set_message_count(
          messaget::M_ERROR, saved_errors);
        defer_auto_return = true;
      }

      get_message_handler().set_verbosity(saved_verbosity);
    }
    else
    {
      // No return statement — deduce void
      function_type.return_type() = void_type();
      return_type = void_type();
    }
  }

  // C++20: generate body for defaulted operator<=>
  if(
    symbol.base_name == "operator<=>" && symbol.value.id() == ID_code &&
    to_code(symbol.value).get_statement() == ID_block &&
    !to_code_block(to_code(symbol.value)).has_operands())
  {
    const irep_idt &class_id = symbol.type.get(ID_C_member_name);
    if(!class_id.empty())
    {
      const symbolt &class_sym = lookup(class_id);
      const auto &fn_params = to_code_type(symbol.type).parameters();
      // Find the parameter name (second param after this)
      irep_idt arg_name;
      if(fn_params.size() >= 2)
        arg_name = fn_params[1].get_base_name();
      if(arg_name.empty())
        arg_name = "#anon_arg0";

      source_locationt loc = symbol.location;
      code_blockt body;
      body.add_source_location() = loc;

      for(const auto &c : to_struct_type(class_sym.type).components())
      {
        if(
          c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
          c.get_bool(ID_is_static) || c.type().id() == ID_code)
          continue;
        if(c.get_base_name() == "@most_derived")
          continue;

        const irep_idt &mem = c.get_base_name();
        cpp_namet lhs(mem, loc);
        exprt rhs(ID_member);
        rhs.add(ID_component_cpp_name, cpp_namet(mem, loc));
        rhs.copy_to_operands(cpp_namet(arg_name, loc).as_expr());
        rhs.add_source_location() = loc;

        typet int_type = signed_int_type();
        binary_relation_exprt lt(lhs.as_expr(), ID_lt, rhs);
        lt.add_source_location() = loc;
        binary_relation_exprt gt(lhs.as_expr(), ID_gt, rhs);
        gt.add_source_location() = loc;
        if_exprt inner(
          std::move(gt), from_integer(1, int_type), from_integer(0, int_type));
        inner.add_source_location() = loc;
        if_exprt cmp(
          std::move(lt), from_integer(-1, int_type), std::move(inner));
        cmp.add_source_location() = loc;

        notequal_exprt ne(cmp, from_integer(0, int_type));
        ne.add_source_location() = loc;
        code_frontend_returnt ret(cmp);
        ret.add_source_location() = loc;
        code_ifthenelset ifs(std::move(ne), std::move(ret));
        ifs.add_source_location() = loc;
        body.add(std::move(ifs));
      }

      code_frontend_returnt ret0(from_integer(0, signed_int_type()));
      ret0.add_source_location() = loc;
      body.add(std::move(ret0));

      symbol.value = std::move(body);
    }
  }

  // C++20: generate body for defaulted operator==
  if(
    symbol.base_name == "operator==" && symbol.value.id() == ID_code &&
    to_code(symbol.value).get_statement() == ID_block &&
    !to_code_block(to_code(symbol.value)).has_operands())
  {
    irep_idt class_id = symbol.type.get(ID_C_member_name);
    // For friend operator==, use the friend class instead
    if(class_id.empty())
      class_id = symbol.type.get(ID_C_class);
    if(!class_id.empty())
    {
      const symbolt &class_sym = lookup(class_id);
      const auto &fn_params = to_code_type(symbol.type).parameters();
      bool is_friend_op = symbol.type.get(ID_C_member_name).empty();
      irep_idt lhs_name, rhs_name;
      if(is_friend_op && fn_params.size() >= 2)
      {
        lhs_name = fn_params[0].get_base_name();
        rhs_name = fn_params[1].get_base_name();
      }
      else if(fn_params.size() >= 2)
      {
        rhs_name = fn_params[1].get_base_name();
      }
      if(is_friend_op && lhs_name.empty())
        lhs_name = "#anon_arg0";
      if(rhs_name.empty())
        rhs_name = "#anon_arg1";

      source_locationt loc = symbol.location;

      // Build conjunction: m1==rhs.m1 && m2==rhs.m2 && ...
      exprt result = true_exprt();
      for(const auto &c : to_struct_type(class_sym.type).components())
      {
        if(
          c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
          c.get_bool(ID_is_static) || c.type().id() == ID_code)
          continue;
        if(c.get_base_name() == "@most_derived")
          continue;

        const irep_idt &mem = c.get_base_name();
        exprt lhs_expr;
        if(is_friend_op)
        {
          lhs_expr = exprt(ID_member);
          lhs_expr.add(ID_component_cpp_name, cpp_namet(mem, loc));
          lhs_expr.copy_to_operands(cpp_namet(lhs_name, loc).as_expr());
          lhs_expr.add_source_location() = loc;
        }
        else
        {
          lhs_expr = cpp_namet(mem, loc).as_expr();
        }
        exprt rhs_expr(ID_member);
        rhs_expr.add(ID_component_cpp_name, cpp_namet(mem, loc));
        rhs_expr.copy_to_operands(cpp_namet(rhs_name, loc).as_expr());
        rhs_expr.add_source_location() = loc;

        equal_exprt eq(std::move(lhs_expr), std::move(rhs_expr));
        eq.add_source_location() = loc;

        if(result.is_true())
          result = std::move(eq);
        else
        {
          and_exprt conj(std::move(result), std::move(eq));
          conj.add_source_location() = loc;
          result = std::move(conj);
        }
      }

      code_blockt body;
      body.add_source_location() = loc;
      code_frontend_returnt ret(std::move(result));
      ret.add_source_location() = loc;
      body.add(std::move(ret));

      symbol.value = std::move(body);
    }
  }

  // C++20: generate body for defaulted operator!=
  if(
    symbol.base_name == "operator!=" && symbol.value.id() == ID_code &&
    to_code(symbol.value).get_statement() == ID_block &&
    !to_code_block(to_code(symbol.value)).has_operands())
  {
    const irep_idt &class_id = symbol.type.get(ID_C_member_name);
    if(!class_id.empty())
    {
      const symbolt &class_sym = lookup(class_id);
      const auto &fn_params = to_code_type(symbol.type).parameters();
      irep_idt arg_name;
      if(fn_params.size() >= 2)
        arg_name = fn_params[1].get_base_name();
      if(arg_name.empty())
        arg_name = "#anon_arg0";

      source_locationt loc = symbol.location;

      // Build: !(m1==rhs.m1 && m2==rhs.m2 && ...)
      exprt eq_result = true_exprt();
      for(const auto &c : to_struct_type(class_sym.type).components())
      {
        if(
          c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
          c.get_bool(ID_is_static) || c.type().id() == ID_code)
          continue;
        if(c.get_base_name() == "@most_derived")
          continue;

        const irep_idt &mem = c.get_base_name();
        cpp_namet lhs(mem, loc);
        exprt rhs(ID_member);
        rhs.add(ID_component_cpp_name, cpp_namet(mem, loc));
        rhs.copy_to_operands(cpp_namet(arg_name, loc).as_expr());
        rhs.add_source_location() = loc;

        equal_exprt eq(lhs.as_expr(), rhs);
        eq.add_source_location() = loc;

        if(eq_result.is_true())
          eq_result = std::move(eq);
        else
        {
          and_exprt conj(std::move(eq_result), std::move(eq));
          conj.add_source_location() = loc;
          eq_result = std::move(conj);
        }
      }

      not_exprt neg(std::move(eq_result));
      neg.add_source_location() = loc;

      code_blockt body;
      body.add_source_location() = loc;
      code_frontend_returnt ret(std::move(neg));
      ret.add_source_location() = loc;
      body.add(std::move(ret));

      symbol.value = std::move(body);
    }
  }

  // [dcl.fct.def.default], [class.copy.ctor]/14: an explicitly-defaulted
  // copy or move constructor memberwise copies/moves the base subobjects and
  // non-static data members.  Generate those initializers here, at
  // conversion time: the class is fully formed (so base/member types are
  // known) and this only runs for constructors actually being elaborated,
  // avoiding eager instantiation pressure during class type-checking (which
  // could otherwise perturb overload resolution in heavy system headers).
  // The body was marked "#defaulted_function" and its sole reference
  // parameter named "ref" when the `= default` definition was type-checked.
  if(
    symbol.value.id() == ID_code &&
    symbol.value.get_bool("#defaulted_function") &&
    to_code(symbol.value).get_statement() == ID_block &&
    to_code_type(symbol.type).return_type().id() == ID_constructor)
  {
    const code_typet &ft = to_code_type(symbol.type);
    const irep_idt class_id = symbol.type.get(ID_C_member_name);
    // implicit this + exactly one reference parameter whose referent is the
    // constructor's own class == the copy/move constructor.  Both the copy
    // constructor (lvalue reference, T&) and the move constructor (rvalue
    // reference, T&&) are handled: for the trivially-copyable members we
    // restrict to below, a memberwise move is a memberwise copy
    // ([class.copy.ctor]/15 -- scalar and pointer members are simply copied),
    // so the same generated body is correct for either.
    if(ft.parameters().size() == 2 && !class_id.empty())
    {
      const typet &pt = ft.parameters()[1].type();
      const bool is_ref_to_self =
        pt.id() == ID_pointer &&
        (pt.get_bool(ID_C_reference) || pt.get_bool(ID_C_rvalue_reference)) &&
        to_pointer_type(pt).base_type().id() == ID_struct_tag &&
        to_struct_tag_type(to_pointer_type(pt).base_type()).get_identifier() ==
          class_id;
      const symbolt *class_symbol = symbol_table.lookup(class_id);
      bool has_virtual_base = false;
      if(class_symbol != nullptr && class_symbol->type.id() == ID_struct)
      {
        // Virtual bases require most-derived construction order
        // ([class.base.init]/7,13); CBMC's virtual-base member handling is
        // independently incomplete, so leave such (rare) defaulted ctors
        // with an empty body rather than emitting unsound copies.
        std::list<irep_idt> vbases;
        get_virtual_bases(to_struct_type(class_symbol->type), vbases);
        has_virtual_base = !vbases.empty();
      }
      // Only generate the memberwise copy/move when every base subobject and
      // non-static data member is trivially copyable: a scalar, an array of
      // such, an empty class, or (recursively) a class all of whose own data
      // members are trivially copyable.  A defaulted copy/move constructor is
      // well-formed irrespective of the class's *other* user-declared
      // constructors, so we deliberately do not gate on cpp_is_pod (which
      // rejects e.g. std::_Rb_tree_iterator merely for having a user-provided
      // converting constructor); we look only at the data members' types.
      // For such members a memberwise move coincides with a memberwise copy
      // ([class.copy.ctor]/15), so default_cpctor's copy initializers are
      // correct for the move constructor too.  A class with a union member
      // (e.g. std::basic_string's small-string buffer) is excluded, which
      // also keeps us away from unmodelled library copies such as
      // std::string's _S_copy_chars / _M_replace.
      bool all_members_trivial = true;
      if(class_symbol != nullptr && class_symbol->type.id() == ID_struct)
      {
        std::set<irep_idt> visiting;
        std::function<bool(const typet &)> is_trivial_copy =
          [&](const typet &t) -> bool
        {
          typet et = t;
          while(et.id() == ID_array)
            et = to_array_type(et).element_type();
          if(
            et.id() == ID_pointer || et.id() == ID_signedbv ||
            et.id() == ID_unsignedbv || et.id() == ID_floatbv ||
            et.id() == ID_fixedbv || et.id() == ID_c_bool ||
            et.id() == ID_bool || et.id() == ID_c_enum ||
            et.id() == ID_c_enum_tag)
            return true;
          if(et.id() == ID_struct_tag)
          {
            const irep_idt tag = to_struct_tag_type(et).get_identifier();
            const symbolt *s = symbol_table.lookup(tag);
            if(s == nullptr || s->type.id() != ID_struct)
              return s != nullptr && cpp_is_pod(s->type);
            // Guard against (pathological) recursive containment.
            if(!visiting.insert(tag).second)
              return true;
            bool ok = true;
            for(const auto &mc : to_struct_type(s->type).components())
            {
              if(
                mc.get_bool(ID_is_static) || mc.get_bool(ID_is_type) ||
                mc.type().id() == ID_code || mc.get_bool(ID_is_vtptr))
                continue;
              if(!is_trivial_copy(mc.type()))
                ok = false;
            }
            visiting.erase(tag);
            return ok;
          }
          return false;
        };
        const struct_typet &st = to_struct_type(class_symbol->type);
        for(const auto &b : st.bases())
          if(!is_trivial_copy(b.type()))
            all_members_trivial = false;
        for(const auto &c : st.components())
        {
          if(
            c.get_bool(ID_is_static) || c.get_bool(ID_is_type) ||
            c.type().id() == ID_code || c.get_bool(ID_from_base) ||
            c.get_bool(ID_is_vtptr))
            continue;
          if(!is_trivial_copy(c.type()))
            all_members_trivial = false;
        }
      }
      if(
        is_ref_to_self && class_symbol != nullptr && !has_virtual_base &&
        all_members_trivial)
      {
        // default_cpctor emits initializers that refer to the source
        // object by the parameter name "ref".  Make "ref" resolve to this
        // constructor's actual parameter for the duration of body
        // type-checking by aliasing it in the function scope.  (Done here,
        // not by renaming the parameter at class-typecheck time, so that
        // class elaboration / overload resolution is left untouched.)
        cpp_idt &ref_id = function_scope.insert(irep_idt{"ref"});
        ref_id.identifier = ft.parameters()[1].get_identifier();
        ref_id.id_class = cpp_idt::id_classt::SYMBOL;
        ref_id.is_member = false;

        cpp_declarationt tmp_cpctor;
        default_cpctor(
          *class_symbol, tmp_cpctor, "ref", pt.get_bool(ID_C_rvalue_reference));
        const irept &inits = tmp_cpctor.declarators()[0].member_initializers();
        // The defaulted constructor's body, at this point, consists solely of
        // the member initializers that move_member_initializers inserted from
        // the (empty) `= default` member-initializer list: for every base and
        // non-static data member, a *default* initializer.  Replacing them
        // wholesale with default_cpctor's memberwise *copy* initializers turns
        // the body into the implicit copy/move constructor
        // ([class.copy.ctor]/14): a default initializer left in place would
        // run after the copy and overwrite it (this is why a plain prepend was
        // not enough for class-typed members, which -- unlike scalars -- do
        // get a default member initializer).
        auto &ops = symbol.value.operands();
        ops.clear();
        for(const auto &init : inits.get_sub())
          ops.push_back(static_cast<const exprt &>(init));
      }
    }
  }

  // [dcl.fct.def.default] + [class.copy.assign]/12-13: an explicitly-defaulted
  // copy/move assignment operator performs memberwise assignment of the base
  // subobjects and non-static data members (the source cast to an xvalue for
  // the move operator, so base/member *move* assignment operators are
  // selected).  Elaborate the body here, at conversion time, exactly like the
  // defaulted copy/move constructor above; without this the `= default` body
  // stays an empty block and the operator silently returns nondet.
  if(
    symbol.value.id() == ID_code &&
    symbol.value.get_bool("#defaulted_function") &&
    to_code(symbol.value).get_statement() == ID_block &&
    !to_code_block(to_code(symbol.value)).has_operands() &&
    symbol.base_name == "operator=")
  {
    const code_typet &ft = to_code_type(symbol.type);
    const irep_idt class_id = symbol.type.get(ID_C_member_name);
    if(ft.parameters().size() == 2 && !class_id.empty())
    {
      const typet &pt = ft.parameters()[1].type();
      const bool is_ref_to_self =
        pt.id() == ID_pointer &&
        (pt.get_bool(ID_C_reference) || pt.get_bool(ID_C_rvalue_reference)) &&
        to_pointer_type(pt).base_type().id() == ID_struct_tag &&
        to_struct_tag_type(to_pointer_type(pt).base_type()).get_identifier() ==
          class_id;
      const symbolt *class_symbol = symbol_table.lookup(class_id);
      if(is_ref_to_self && class_symbol != nullptr)
      {
        // default_assignop_value refers to the source by the parameter name
        // "ref"; alias it to this operator's actual parameter (see the
        // defaulted-constructor elaboration above).
        cpp_idt &ref_id = function_scope.insert(irep_idt{"ref"});
        ref_id.identifier = ft.parameters()[1].get_identifier();
        ref_id.id_class = cpp_idt::id_classt::SYMBOL;
        ref_id.is_member = false;

        cpp_declaratort tmp_declarator;
        tmp_declarator.add_source_location() = symbol.location;
        default_assignop_value(
          *class_symbol, tmp_declarator, pt.get_bool(ID_C_rvalue_reference));
        symbol.value = tmp_declarator.value();
      }
    }
  }

  // [temp.deduct]/8 and the system-header analogue: when the
  // function whose body we are elaborating lives in a system
  // header, any typecheck failure is treated as SFINAE rather
  // than a user-visible compilation error.  This matches what
  // conforming implementations do when a non-template system
  // header function happens to be ill-formed against CBMC's
  // (deliberately incomplete) model of system headers — the
  // caller gets a "no usable body" symbol rather than a
  // diagnostic attributed to the header.
  //
  // User-code bodies use normal error propagation below.
  const std::string body_file = id2string(symbol.location.get_file());
  const bool is_system_header_body =
    body_file.find("/usr/include/") == 0 || body_file.find("/usr/lib/") == 0;

  std::optional<sfinae_contextt> syshdr_guard;
  if(is_system_header_body)
    syshdr_guard.emplace(*this);

  try
  {
    typecheck_code(to_code(symbol.value));
  }
  catch(int)
  {
    // For system headers, clear the broken body and return.
    // For user code, re-throw.  The `syshdr_guard` destructor (if
    // engaged) runs on the way out and restores handler/error
    // count; the user-code rethrow keeps going to the caller.
    if(is_system_header_body)
    {
      // Before giving up: a class-template instance member can be left with
      // the WRONG overload's out-of-line body (attached by an earlier
      // base-name-only match), e.g. the input-iterator basic_string::
      // _M_construct body (which references `__beg`) ending up on the fill
      // _M_construct(size_type, _CharT) member, so its conversion fails with
      // "symbol '__beg' is unknown" and the member silently becomes a no-op.
      // If a *unique* out-of-line definition whose signature (parameter
      // arity) matches this member exists, and it is a different definition
      // from the one currently attached (different source location), adopt
      // that signature-matched body and the definition's parameter names and
      // re-type-check.  Doing this only on failure leaves correctly-converting
      // members untouched.  Per N5008 [over.match] the definition belonging to
      // a member is the one whose signature matches it; per [dcl.fct]/3
      // parameter names are not part of the type, so the body must use the
      // definition's names.
      if(!symbol.type.get(ID_C_member_name).empty())
      {
        std::vector<irep_idt> def_param_names;
        const std::optional<exprt> matched =
          instantiate_matching_member_body(symbol, def_param_names);
        if(
          matched.has_value() &&
          !matched->source_location().get_line().empty() &&
          matched->source_location().get_line() !=
            symbol.value.source_location().get_line())
        {
          symbol.value = *matched;
          code_typet::parameterst &params = function_type.parameters();
          const std::size_t off =
            (!params.empty() && params.front().get_this()) ? 1 : 0;
          for(std::size_t i = 0;
              i < def_param_names.size() && off + i < params.size();
              ++i)
          {
            if(!def_param_names[i].empty())
              params[off + i].set_base_name(def_param_names[i]);
          }
          // Re-type-check with the corrected body in a fresh scope.  The
          // source-location guard above prevents this from looping: after the
          // adoption the attached body's location equals the match's.  If the
          // corrected body still cannot be converted (e.g. it transitively
          // instantiates something CBMC cannot model), fall back to the
          // no-body state exactly as if no repair had been attempted, so the
          // repair can never make a system-header member worse.
          functions_being_typechecked.erase(symbol.name);
          try
          {
            convert_function(symbol);
            return;
          }
          catch(...)
          {
            // fall through to the no-body state below
          }
        }
      }
      symbol.value.make_nil();
      functions_being_typechecked.erase(symbol.name);
      return;
    }
    throw;
  }

  // Deferred auto return type deduction: the initial attempt failed
  // (e.g., if constexpr with type-dependent discarded branch).
  // Now that the body is type-checked, find a return statement in the
  // surviving branches.
  if(defer_auto_return)
  {
    std::function<const typet *(const codet &)> find_return_type =
      [&](const codet &code) -> const typet *
    {
      if(code.get_statement() == ID_return && code.operands().size() == 1)
      {
        return &code.op0().type();
      }
      for(const auto &op : code.operands())
      {
        if(op.id() == ID_code)
        {
          const typet *r = find_return_type(to_code(op));
          if(r != nullptr)
            return r;
        }
      }
      return nullptr;
    };

    const typet *deduced = find_return_type(to_code(symbol.value));
    if(deduced != nullptr)
    {
      function_type.return_type() = *deduced;
      return_type = *deduced;
    }
    else
    {
      function_type.return_type() = void_type();
      return_type = void_type();
    }
  }

  symbol.value.type()=symbol.type;

  disable_access_control = saved_access_control;

  deferred_typechecking.erase(symbol.name);
  functions_being_typechecked.erase(symbol.name);
}

/// for function overloading
irep_idt cpp_typecheckt::function_identifier(const typet &type)
{
  const code_typet &function_type=
    to_code_type(template_subtype(type));

  const code_typet::parameterst &parameters=
    function_type.parameters();

  std::string result;
  bool first=true;

  result+='(';

  // the name of the function should not depend on
  // the class name that is encoded in the type of this,
  // but we must distinguish "const" and "non-const" member
  // functions

  code_typet::parameterst::const_iterator it=
    parameters.begin();

  if(it != parameters.end() && it->get_this())
  {
    const typet &pointer=it->type();
    const typet &symbol = to_pointer_type(pointer).base_type();
    if(symbol.get_bool(ID_C_constant))
      result += "$const";
    if(symbol.get_bool(ID_C_volatile))
      result += "$volatile";
    result += id2string(ID_this);
    first=false;
    it++;
  }

  // we skipped the "this", on purpose!

  for(; it!=parameters.end(); it++)
  {
    if(first)
      first=false;
    else
      result+=',';
    typet tmp_type=it->type();
    // C/C++ function parameters of function type decay to
    // pointer-to-function.  Normalise here so that the identifier
    // is the same regardless of declaration style.
    if(tmp_type.id() == ID_code)
      tmp_type = pointer_type(tmp_type);
    // Top-level const/volatile on parameters does not affect the
    // function signature per [dcl.fct]/5.
    tmp_type.remove(ID_C_constant);
    tmp_type.remove(ID_C_volatile);
    result += cpp_type2name(tmp_type);
  }

  result+=')';

  return result;
}
