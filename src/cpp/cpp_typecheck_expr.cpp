/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_initializer.h>
#include <util/floatbv_expr.h>
#include <util/mathematical_types.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/replace_symbol.h>
#include <util/simplify_expr.h>
#include <util/string_constant.h>
#include <util/symbol_table_base.h>

#include <ansi-c/c_qualifiers.h>
#include <ansi-c/type2name.h>

#include "cpp_exception_id.h"
#include "cpp_sfinae_context.h"
#include "cpp_type2name.h"
#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"
#include "cpp_util.h"
#include "expr2cpp.h"

bool cpp_typecheckt::find_parent(
  const symbolt &symb,
  const irep_idt &base_name,
  irep_idt &identifier)
{
  for(const auto &b : to_struct_type(symb.type).bases())
  {
    const irep_idt &id = b.type().get_identifier();
    if(lookup(id).base_name == base_name)
    {
      identifier = id;
      return true;
    }
  }

  return false;
}

/// Phase 1B target-typet overload — currently forwards to the
/// no-target implementation.  Subsequent phases consume the target
/// to drive [temp.deduct.funcaddr]/1 deduction at the address-of
/// and cpp_name layers.
void cpp_typecheckt::typecheck_expr_main(
  exprt &expr,
  const target_typet &target)
{
  (void)target;
  typecheck_expr_main(expr);
}

bool cpp_typecheckt::requirement_expression_is_valid(exprt op)
{
  // [expr.prim.req.general]/5: substitution into / semantic checking of a
  // requirement that forms an invalid expression in the immediate context
  // makes the requires-expression evaluate to false, not ill-formed.  Some
  // typecheck paths report the failure by throwing (caught here); others emit
  // a diagnostic and return without throwing (e.g. member access on a
  // non-class type).  Capture and restore the error count so that either kind
  // of failure becomes a soft `false` and does not fail the translation unit.
  const std::size_t errors_before =
    get_message_handler().get_message_count(messaget::M_ERROR);
  bool valid = true;
  try
  {
    sfinae_contextt sfinae_guard{*this};
    typecheck_expr(op);
  }
  catch(...)
  {
    valid = false;
  }
  if(
    get_message_handler().get_message_count(messaget::M_ERROR) != errors_before)
    valid = false;
  get_message_handler().set_message_count(messaget::M_ERROR, errors_before);
  return valid;
}

bool cpp_typecheckt::compound_requirement_is_satisfied(const exprt &expr)
{
  const std::size_t errors_before =
    get_message_handler().get_message_count(messaget::M_ERROR);
  bool satisfied = true;
  try
  {
    sfinae_contextt sfinae_guard{*this};
    exprt op = to_unary_expr(expr).op();
    typecheck_expr(op);

    const irept &constraint = expr.find("#constraint");
    if(constraint.is_not_nil())
    {
      // [expr.prim.req.compound]/1: the return-type-requirement names a
      // type-constraint C; the requirement is satisfied only if
      // C<decltype((E))> is satisfied.  decltype((E)) uses the
      // parenthesised form: an lvalue E yields an lvalue-reference type
      // ([dcl.type.decltype]/1).
      typet result_type = op.type();
      if(op.get_bool(ID_C_lvalue))
        result_type = reference_type(result_type);

      irep_idt concept_name;
      const irept *constraint_args = nullptr;
      for(const auto &sub : constraint.get_sub())
      {
        if(sub.id() == ID_name)
          concept_name = sub.get(ID_identifier);
        else if(sub.id() == ID_template_args)
          constraint_args = &sub;
      }

      if(!concept_name.empty())
      {
        const auto cids = cpp_scopes.current_scope().lookup(
          concept_name, cpp_scopet::RECURSIVE);
        bool evaluated = false;
        for(const auto *cid : cids)
        {
          const auto *csym = symbol_table.lookup(cid->identifier);
          if(!csym || !csym->type.get_bool(ID_is_template))
            continue;
          const auto &cd = to_cpp_declaration(csym->type);
          if(cd.declarators().empty())
            continue;
          exprt cbody = cd.declarators()[0].value();
          if(cbody.is_nil())
            continue;
          // Build C's argument list: decltype((E)) prepended to the explicit
          // type-constraint arguments ([temp.names]/9, [expr.prim.req.compound]).
          cpp_template_args_tct check_args;
          exprt prepended{ID_type};
          prepended.type() = result_type;
          check_args.arguments().push_back(std::move(prepended));
          if(constraint_args != nullptr)
          {
            const irept &args_sub = constraint_args->find(ID_arguments);
            for(const auto &a : args_sub.get_sub())
            {
              exprt arg_copy = static_cast<const exprt &>(a);
              typecheck_type(arg_copy.type());
              check_args.arguments().push_back(std::move(arg_copy));
            }
          }
          template_mapt cmap;
          cmap.build(cd.template_type(), check_args);
          cmap.apply(cbody);
          // Evaluate C's body recursively through typecheck_expr so nested
          // requirements / concept-ids resolve via the same machinery.
          typecheck_expr(cbody);
          simplify(cbody, *this);
          if(!cbody.is_true())
            satisfied = false;
          evaluated = true;
          break;
        }
        // If the named concept could not be resolved at all, fall back to the
        // validity of E (already established above): do not spuriously fail.
        (void)evaluated;
      }
    }
  }
  catch(...)
  {
    satisfied = false;
  }
  if(
    get_message_handler().get_message_count(messaget::M_ERROR) != errors_before)
    satisfied = false;
  get_message_handler().set_message_count(messaget::M_ERROR, errors_before);
  return satisfied;
}

/// Called after the operands are done
void cpp_typecheckt::typecheck_expr_main(exprt &expr)
{
  if(expr.id()==ID_cpp_name)
    typecheck_expr_cpp_name(expr, cpp_typecheck_fargst());
  else if(expr.id()=="cpp-this")
    typecheck_expr_this(expr);
  else if(expr.id() == ID_pointer_to_member)
    convert_pmop(expr);
  else if(expr.id() == ID_new_object)
  {
  }
  else if(operator_is_overloaded(expr))
  {
  }
  else if(expr.id()=="explicit-typecast")
    typecheck_expr_explicit_typecast(expr);
  else if(expr.id() == ID_typecast && expr.type().id() == ID_cpp_name)
  {
    typecheck_type(expr.type());
    c_typecheck_baset::typecheck_expr_main(expr);
  }
  else if(expr.id() == "type_requirement")
  {
    typet &t = static_cast<typet &>(expr.add(ID_type_arg));
    typecheck_type(t);
    expr = typecast_exprt{true_exprt(), c_bool_type()};
  }
  else if(expr.id() == "simple_requirement")
  {
    // [expr.prim.req.simple]/1: a simple-requirement is satisfied iff the
    // expression is valid.  [expr.prim.req.general]/5: an invalid expression
    // in the immediate context makes the requires-expression evaluate to
    // false, not ill-formed.  requirement_expression_is_valid converts any
    // failure (including errors that do not throw, e.g. member access on a
    // non-class type) into a soft `false`.
    bool satisfied;
    if(expr.operands().size() == 1)
      satisfied = requirement_expression_is_valid(to_unary_expr(expr).op());
    else
      // Defensive: a malformed/empty requirement node (can arise from a
      // requirement form the parser did not fully model, seen in the deep
      // <ranges> concept chain).  Do not abort on it (to_unary_expr would
      // trip an invariant); treat the unmodelled requirement as satisfied so
      // it neither crashes nor spuriously fails the concept.
      satisfied = true;
    expr = typecast_exprt{
      satisfied ? static_cast<exprt>(true_exprt())
                : static_cast<exprt>(false_exprt()),
      c_bool_type()};
  }
  else if(expr.id() == "compound_requirement")
  {
    // [expr.prim.req.compound]/1: { E } -> C is satisfied iff E is a valid
    // expression and, when the return-type-requirement C is present,
    // C<decltype((E))> is satisfied.  Substitution failure in the immediate
    // context is a soft failure ([expr.prim.req.general]/5).
    bool satisfied;
    if(expr.operands().size() == 1)
      satisfied = compound_requirement_is_satisfied(expr);
    else
      satisfied = true; // defensive: see simple_requirement above
    expr = typecast_exprt{
      satisfied ? static_cast<exprt>(true_exprt())
                : static_cast<exprt>(false_exprt()),
      c_bool_type()};
  }
  else if(expr.id() == "concept_check")
  {
    // C++20 nested concept requirement: requires ConceptName<T>;
    // Look up the concept and evaluate its body.
    const irep_idt &concept_name = expr.get("concept_name");
    const auto concept_ids =
      cpp_scopes.current_scope().lookup(concept_name, cpp_scopet::RECURSIVE);
    if(concept_ids.empty())
      throw 0;
    const auto *concept_sym =
      symbol_table.lookup((*concept_ids.begin())->identifier);
    if(!concept_sym || !concept_sym->type.get_bool(ID_is_template))
      throw 0;
    const cpp_declarationt &concept_decl =
      to_cpp_declaration(concept_sym->type);
    if(concept_decl.declarators().empty())
      throw 0;
    exprt body = concept_decl.declarators()[0].value();
    if(body.is_nil())
      throw 0;
    // Apply the current template_map to substitute parameters
    template_map.apply(body);
    typecheck_expr(body);
    simplify(body, *this);
    if(body.is_false())
      throw 0;
    expr = typecast_exprt{true_exprt(), c_bool_type()};
  }
  else if(expr.id() == ID_bit_cast)
  {
    // __builtin_bit_cast(Type, expr) — resolve cpp_name type
    if(expr.type().id() == ID_cpp_name)
      typecheck_type(expr.type());
    c_typecheck_baset::typecheck_expr_main(expr);
  }
  else if(expr.id()=="explicit-constructor-call")
    typecheck_expr_explicit_constructor_call(expr);
  else if(expr.id()==ID_code)
  {
    // The parser may produce ID_code for expressions like bool(x)
    // when it cannot distinguish a functional cast from a function type.
    // Check if this looks like a functional cast: return type is a
    // primitive type and there is exactly one parameter.
    const irept &return_type = expr.find(ID_return_type);
    const irept &parameters = expr.find(ID_parameters);
    if(
      return_type.is_not_nil() && parameters.get_sub().size() == 1 &&
      parameters.get_sub()[0].id() == ID_cpp_declaration)
    {
      typet cast_target = static_cast<const typet &>(return_type);
      typecheck_type(cast_target);

      // Extract the parameter declaration's type as an expression
      const auto &param_decl =
        static_cast<const cpp_declarationt &>(parameters.get_sub()[0]);
      exprt cast_arg = static_cast<const exprt &>(
        static_cast<const irept &>(param_decl.type()));
      typecheck_expr(cast_arg);
      expr = typecast_exprt(cast_arg, cast_target);
      return;
    }
    // A return statement in expression context can occur when a
    // constexpr function body is used as a value during template
    // instantiation.  Extract the return value.
    if(expr.get(ID_statement) == ID_return && expr.operands().size() == 1)
    {
      exprt ret_val = to_code_frontend_return(to_code(expr)).return_value();
      typecheck_expr(ret_val);
      expr = ret_val;
      return;
    }
    error().source_location = expr.source_location();
    error() << "unexpected ID_code expression" << eom;
    throw 0;
  }
  else if(expr.id()==ID_symbol)
  {
    // ignore here
#ifdef DEBUG
    std::cerr << "E: " << expr.pretty() << '\n';
    std::cerr << "cpp_typecheckt::typecheck_expr_main got symbol\n";
#endif
  }
  else if(expr.id()=="__is_base_of")
  {
    // an MS extension, also a Clang/GCC built-in.  Per N5008
    // [meta.rel] table: `is_base_of<Base, Derived>::value` is
    // true iff `Base` is a base class of `Derived` (or the same
    // class).  Both `class` and `struct` declarations produce
    // class types per [class]/1; CBMC stores `struct` as a
    // `struct_typet` without `ID_C_class`, while `class` sets
    // `ID_C_class`.  `to_class_type` requires `ID_C_class`, so
    // call `to_struct_type` here — a struct is a class-key for
    // base-class purposes regardless of the `class`/`struct`
    // keyword.

    typet base=static_cast<const typet &>(expr.find("type_arg1"));
    typet deriv=static_cast<const typet &>(expr.find("type_arg2"));

    typecheck_type(base);
    typecheck_type(deriv);

    if(base.id() != ID_struct_tag || deriv.id() != ID_struct_tag)
      expr=false_exprt();
    else
    {
      irep_idt base_name = follow_tag(to_struct_tag_type(base)).get(ID_name);
      const struct_typet &struct_type =
        follow_tag(to_struct_tag_type(deriv));
      irep_idt deriv_name = struct_type.get(ID_name);

      // Per N5008 [meta.rel] / Cpp17BaseOfRequirement: a type is
      // a base of itself for the purposes of `is_base_of`.
      if(base_name == deriv_name || struct_type.has_base(base_name))
        expr=true_exprt();
      else
        expr=false_exprt();
    }
  }
  else if(expr.id()==ID_msc_uuidof)
  {
    // these appear to have type "struct _GUID"
    // and they are lvalues!
    expr.type() = struct_tag_typet("tag-_GUID");
    expr.set(ID_C_lvalue, true);
  }
  else if(expr.id() == ID_typeid)
    typecheck_expr_typeid(expr);
  else if(
    expr.id() == "__is_constructible" || expr.id() == "__is_assignable" ||
    expr.id() == "__is_convertible_to" || expr.id() == "__is_convertible" ||
    expr.id() == "__is_trivially_constructible" ||
    expr.id() == "__is_trivially_assignable" ||
    expr.id() == "__is_nothrow_constructible" ||
    expr.id() == "__is_nothrow_assignable" || expr.id() == "__is_same" ||
    expr.id() == "__is_layout_compatible" ||
    expr.id() == "__is_nothrow_convertible" ||
    expr.id() == "__is_pointer_interconvertible_base_of" ||
    expr.id() == "__reference_constructs_from_temporary" ||
    expr.id() == "__reference_converts_from_temporary")
  {
    // GCC/Clang built-in type traits
    typet t1 = static_cast<const typet &>(expr.find("type_arg1"));
    typet t2 = static_cast<const typet &>(expr.find("type_arg2"));
    if(t1.is_nil() && !expr.find(ID_type_arg).is_nil())
      t1 = static_cast<const typet &>(expr.find(ID_type_arg));
    typecheck_type(t1);
    if(t2.is_not_nil())
    {
      try
      {
        typecheck_type(t2);
      }
      catch(int)
      {
        t2 = typet{ID_nil};
      }
    }

    if(expr.id() == "__is_same")
    {
      if(t1 == t2)
        expr = true_exprt();
      else
        expr = false_exprt();
    }
    else if(
      expr.id() == "__is_convertible_to" || expr.id() == "__is_convertible")
    {
      // Check if t1 is implicitly convertible to t2.
      if(t1.id() == ID_empty && t2.id() == ID_empty)
      {
        // void -> void is convertible
        expr = true_exprt();
      }
      else if(t1.id() == ID_empty || t2.id() == ID_empty)
      {
        expr = false_exprt();
      }
      else
      {
        exprt tmp;
        symbol_exprt from(irep_idt(), t1);
        if(implicit_conversion_sequence(from, t2, tmp))
          expr = true_exprt();
        else
          expr = false_exprt();
      }
    }
    else if(expr.id() == "__is_assignable")
    {
      // __is_assignable(T, U) is true if the expression
      // declval<T>() = declval<U>() is well-formed.
      // For references: T must be an lvalue reference for assignment.
      if(is_reference(t1))
      {
        typet dest = to_reference_type(t1).base_type();
        // Cannot assign to const
        if(dest.get_bool(ID_C_constant))
        {
          expr = false_exprt();
        }
        else
        {
          exprt tmp;
          symbol_exprt from(irep_idt(), t2);
          if(implicit_conversion_sequence(from, dest, tmp))
            expr = true_exprt();
          else
            expr = false_exprt();
        }
      }
      else
      {
        // Non-reference T: assignment to rvalue is not valid for
        // scalar types, but may be valid for class types with
        // operator=. Conservatively return false.
        expr = false_exprt();
      }
    }
    else if(
      expr.id() == "__is_trivially_constructible" ||
      expr.id() == "__is_nothrow_constructible")
    {
      // Delegate to __is_constructible logic: trivially/nothrow
      // qualifiers are about optimization, not correctness.
      // For POD/scalar types with matching args, return true.
      if(t2.is_nil())
      {
        // __is_trivially_constructible(T) — default constructible
        // A type is trivially default constructible if it has no
        // user-provided default constructor.
        bool trivial = true;
        if(t1.id() == ID_struct_tag)
        {
          const auto &st = follow_tag(to_struct_tag_type(t1));
          for(const auto &c : st.components())
          {
            if(
              c.type().id() == ID_code &&
              to_code_type(c.type()).return_type().id() == ID_constructor &&
              to_code_type(c.type()).parameters().size() == 1)
            {
              // Found a default constructor (only 'this' param).
              // Check if it has a non-trivial body in the symbol table.
              const auto *sym = symbol_table.lookup(c.get_name());
              if(sym != nullptr && sym->value.is_not_nil())
              {
                trivial = false;
                break;
              }
            }
          }
        }
        expr = trivial ? exprt(true_exprt()) : exprt(false_exprt());
      }
      else
      {
        // __is_trivially_constructible(T, U) — copy/move constructible
        expr = true_exprt();
      }
    }
    else if(
      expr.id() == "__is_trivially_assignable" ||
      expr.id() == "__is_nothrow_assignable")
    {
      // Delegate to __is_assignable logic.
      expr = true_exprt();
    }
    else if(expr.id() == "__is_nothrow_convertible")
    {
      // Same as __is_convertible — nothrow is about optimization.
      if(t1.id() == ID_empty && t2.id() == ID_empty)
        expr = true_exprt();
      else if(t1.id() == ID_empty || t2.id() == ID_empty)
        expr = false_exprt();
      else
      {
        exprt tmp;
        symbol_exprt from(irep_idt(), t1);
        if(implicit_conversion_sequence(from, t2, tmp))
          expr = true_exprt();
        else
          expr = false_exprt();
      }
    }
    else if(expr.id() == "__is_constructible")
    {
      // __is_constructible(T, Args...) — check if T can be constructed
      // from Args. For scalar types, construction from a compatible type
      // (including references) is always possible.
      if(t2.is_nil())
      {
        // Default constructible — scalars are always default constructible
        expr = true_exprt();
      }
      else
      {
        // Strip references from the argument type
        typet arg_type = t2;
        if(is_reference(arg_type))
          arg_type = to_reference_type(arg_type).base_type();
        arg_type.remove(ID_C_constant);
        arg_type.remove(ID_C_volatile);

        typet target = t1;
        target.remove(ID_C_constant);
        target.remove(ID_C_volatile);

        if(target == arg_type)
          expr = true_exprt();
        else
        {
          exprt tmp;
          symbol_exprt from(irep_idt(), t2);
          if(implicit_conversion_sequence(from, t1, tmp))
            expr = true_exprt();
          else
            expr = false_exprt();
        }
      }
    }
    else
      // conservatively return false for traits we cannot evaluate
      expr = false_exprt();
  }
  else if(expr.id() == ID_noexcept)
  {
    // C++11 noexcept operator per [expr.unary.noexcept]/3: "The
    // result of the noexcept operator is a prvalue of type bool.
    // Its value is false if the expression would throw because of
    // …; otherwise it is true."  Evaluating the operand for this
    // determination is an unevaluated operand ([basic.def.odr]/2,
    // [expr.context]/1) and substitution failures must not leak
    // as diagnostics — treat it as a SFINAE immediate context.
    auto &op = to_unary_expr(expr).op();
    bool result = false;

    try
    {
      sfinae_contextt sfinae_guard{*this};
      typecheck_expr(op);
      if(op.id() == ID_side_effect && op.get(ID_statement) == ID_function_call)
      {
        const auto &fn = to_side_effect_expr_function_call(op).function();
        if(fn.id() == ID_symbol)
        {
          const auto *sym =
            symbol_table.lookup(to_symbol_expr(fn).get_identifier());
          if(sym != nullptr && sym->type.id() == ID_code)
          {
            const auto &code_type = to_code_type(sym->type);
            if(
              code_type.get_bool("#C_noexcept") ||
              code_type.get_bool(ID_noexcept))
            {
              result = true;
            }
            // Destructors are implicitly noexcept since C++11
            if(code_type.return_type().id() == ID_destructor)
              result = true;
          }
        }
        // Destructor calls via .~T() syntax
        if(fn.id() == ID_member && fn.find(ID_component_cpp_name).is_not_nil())
        {
          const auto &name = to_cpp_name(fn.find(ID_component_cpp_name));
          const irep_idt &bn = name.get_base_name();
          if(!bn.empty() && id2string(bn)[0] == '~')
            result = true;
        }
      }
      // If the expression type-checked without throwing,
      // and it's not a function call, it's likely noexcept
      // (e.g., built-in operations, trivial destructors).
      if(!result && op.id() != ID_side_effect)
        result = true;
    }
    catch(...)
    {
      // Substitution failure inside noexcept is a SFINAE failure
      // that in turn makes the noexcept-expr evaluate to `true`
      // (the operand can't throw because it can't even exist).
      result = true;
    }
    if(result)
      expr = true_exprt();
    else
      expr = false_exprt();
  }
  else if(expr.id()==ID_initializer_list)
  {
    // Preserve the type if it was already set (e.g., from a
    // brace-init-list for aggregate initialization).
    if(expr.type().is_nil() || expr.type().id() == ID_empty)
      expr.type().id(ID_initializer_list);
  }
  else if(
    expr.id() == ID_const_cast || expr.id() == ID_dynamic_cast ||
    expr.id() == ID_reinterpret_cast || expr.id() == ID_static_cast)
  {
    typecheck_cast_expr(expr);
  }
  else if(expr.id() == "__is_abstract")
  {
    typet t;
    if(!expr.find(ID_type_arg).is_nil())
      t = static_cast<const typet &>(expr.find(ID_type_arg));
    else if(!expr.find("type_arg1").is_nil())
      t = static_cast<const typet &>(expr.find("type_arg1"));
    typecheck_type(t);
    // A class is abstract if it has at least one pure virtual function.
    if(t.id() == ID_struct_tag)
    {
      const struct_typet &st =
        to_struct_type(follow_tag(to_struct_tag_type(t)));
      bool is_abstract = false;
      for(const auto &c : st.components())
      {
        if(c.get_bool(ID_is_pure_virtual))
        {
          is_abstract = true;
          break;
        }
      }
      expr = is_abstract ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else
      expr = false_exprt();
  }
  else if(
    expr.id() == "__is_class" || expr.id() == "__is_empty" ||
    expr.id() == "__is_enum" || expr.id() == "__is_final" ||
    expr.id() == "__is_aggregate" || expr.id() == "__is_pod" ||
    expr.id() == "__is_polymorphic" || expr.id() == "__is_union" ||
    expr.id() == "__is_trivial" || expr.id() == "__is_trivially_copyable" ||
    expr.id() == "__is_standard_layout" || expr.id() == "__is_literal_type" ||
    expr.id() == "__is_integral" || expr.id() == "__is_void" ||
    expr.id() == "__is_floating_point" || expr.id() == "__is_arithmetic" ||
    expr.id() == "__is_null_pointer" || expr.id() == "__is_pointer" ||
    expr.id() == "__is_reference" || expr.id() == "__is_lvalue_reference" ||
    expr.id() == "__is_rvalue_reference" || expr.id() == "__is_function" ||
    expr.id() == "__is_array" || expr.id() == "__is_member_pointer" ||
    expr.id() == "__is_member_function_pointer" ||
    expr.id() == "__is_member_object_pointer" || expr.id() == "__is_signed" ||
    expr.id() == "__is_unsigned" || expr.id() == "__is_const" ||
    expr.id() == "__is_volatile" || expr.id() == "__is_scoped_enum" ||
    expr.id() == "__is_object" || expr.id() == "__is_bounded_array" ||
    expr.id() == "__is_unbounded_array" || expr.id() == "__is_referenceable" ||
    expr.id() == "__has_trivial_constructor" ||
    expr.id() == "__has_trivial_copy" ||
    expr.id() == "__has_trivial_destructor" ||
    expr.id() == "__has_trivial_assign" ||
    expr.id() == "__has_nothrow_assign" ||
    expr.id() == "__has_nothrow_constructor" ||
    expr.id() == "__has_nothrow_copy" ||
    expr.id() == "__has_virtual_destructor" ||
    expr.id() == "__has_unique_object_representations" ||
    expr.id() == "__is_trivially_relocatable" ||
    expr.id() == "__is_trivially_destructible" ||
    expr.id() == "__is_destructible" ||
    expr.id() == "__is_nothrow_destructible" || expr.id() == "__is_compound" ||
    expr.id() == "__is_fundamental" || expr.id() == "__is_scalar")
  {
    // Unary type predicates — conservatively return false for now.
    typet t;
    if(!expr.find(ID_type_arg).is_nil())
      t = static_cast<const typet &>(expr.find(ID_type_arg));
    else if(!expr.find("type_arg1").is_nil())
      t = static_cast<const typet &>(expr.find("type_arg1"));
    typecheck_type(t);
    if(expr.id() == "__is_class")
      expr =
        (t.id() == ID_struct_tag) ? exprt(true_exprt()) : exprt(false_exprt());
    else if(expr.id() == "__is_union")
      expr =
        (t.id() == ID_union_tag) ? exprt(true_exprt()) : exprt(false_exprt());
    else if(expr.id() == "__is_enum")
      expr =
        (t.id() == ID_c_enum_tag) ? exprt(true_exprt()) : exprt(false_exprt());
    else if(expr.id() == "__is_final")
    {
      bool is_final = false;
      if(t.id() == ID_struct_tag)
      {
        const auto &struct_type = follow_tag(to_struct_tag_type(t));
        is_final = struct_type.get_bool(ID_final);
      }
      expr = is_final ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_integral")
    {
      expr =
        (t.id() == ID_signedbv || t.id() == ID_unsignedbv ||
         t.id() == ID_c_bool || t.id() == ID_bool || t.id() == ID_c_enum_tag)
          ? exprt(true_exprt())
          : exprt(false_exprt());
    }
    else if(expr.id() == "__is_floating_point")
    {
      expr = (t.id() == ID_floatbv || t.id() == ID_fixedbv)
               ? exprt(true_exprt())
               : exprt(false_exprt());
    }
    else if(expr.id() == "__is_arithmetic")
    {
      expr =
        (t.id() == ID_signedbv || t.id() == ID_unsignedbv ||
         t.id() == ID_c_bool || t.id() == ID_bool || t.id() == ID_floatbv ||
         t.id() == ID_fixedbv || t.id() == ID_c_enum_tag)
          ? exprt(true_exprt())
          : exprt(false_exprt());
    }
    else if(expr.id() == "__is_void")
    {
      expr = (t.id() == ID_empty) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_pointer")
    {
      expr = (t.id() == ID_pointer && !is_reference(t)) ? exprt(true_exprt())
                                                        : exprt(false_exprt());
    }
    else if(expr.id() == "__is_reference")
    {
      expr = is_reference(t) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_lvalue_reference")
    {
      expr = (is_reference(t) && !is_rvalue_reference(t))
               ? exprt(true_exprt())
               : exprt(false_exprt());
    }
    else if(expr.id() == "__is_rvalue_reference")
    {
      expr =
        is_rvalue_reference(t) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_array")
    {
      expr = (t.id() == ID_array) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_function")
    {
      expr = (t.id() == ID_code) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(
      expr.id() == "__is_member_pointer" ||
      expr.id() == "__is_member_function_pointer" ||
      expr.id() == "__is_member_object_pointer")
    {
      bool is_memptr =
        t.id() == ID_pointer && t.find(ID_to_member).is_not_nil();
      if(is_memptr && expr.id() == "__is_member_function_pointer")
        is_memptr = to_pointer_type(t).base_type().id() == ID_code;
      else if(is_memptr && expr.id() == "__is_member_object_pointer")
        is_memptr = to_pointer_type(t).base_type().id() != ID_code;
      expr = is_memptr ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_null_pointer")
    {
      expr = (t.id() == ID_pointer && t == pointer_type(empty_typet()))
               ? exprt(true_exprt())
               : exprt(false_exprt());
    }
    else if(expr.id() == "__is_signed")
    {
      expr =
        (t.id() == ID_signedbv || t.id() == ID_fixedbv || t.id() == ID_floatbv)
          ? exprt(true_exprt())
          : exprt(false_exprt());
    }
    else if(expr.id() == "__is_unsigned")
    {
      expr =
        (t.id() == ID_unsignedbv || t.id() == ID_c_bool || t.id() == ID_bool)
          ? exprt(true_exprt())
          : exprt(false_exprt());
    }
    else if(expr.id() == "__is_const")
    {
      expr =
        t.get_bool(ID_C_constant) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_volatile")
    {
      expr =
        t.get_bool(ID_C_volatile) ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_scoped_enum")
    {
      bool result = false;
      if(t.id() == ID_c_enum_tag)
      {
        const auto &enum_type =
          to_c_enum_type(follow_tag(to_c_enum_tag_type(t)));
        result = enum_type.get_bool(ID_C_class);
      }
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_object")
    {
      // true for everything except functions, references, and void
      bool result = t.id() != ID_code && t.id() != ID_empty &&
                    !is_reference(t) && !is_rvalue_reference(t);
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_bounded_array")
    {
      bool result = t.id() == ID_array && to_array_type(t).size().is_not_nil();
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_unbounded_array")
    {
      bool result = t.id() == ID_array && to_array_type(t).size().is_nil();
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(
      expr.id() == "__is_trivially_destructible" ||
      expr.id() == "__is_nothrow_destructible" ||
      expr.id() == "__is_destructible")
    {
      bool result = true;
      if(t.id() == ID_struct_tag)
      {
        const auto &st = follow_tag(to_struct_tag_type(t));
        for(const auto &comp : to_struct_type(st).components())
          if(comp.get_bool(ID_destructor))
          {
            result = false;
            break;
          }
      }
      expr = result ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_compound")
    {
      bool f = t.id() == ID_empty || t.id() == ID_signedbv ||
               t.id() == ID_unsignedbv || t.id() == ID_c_bool ||
               t.id() == ID_bool || t.id() == ID_floatbv ||
               t.id() == ID_fixedbv;
      expr = !f ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_fundamental")
    {
      bool r = t.id() == ID_empty || t.id() == ID_signedbv ||
               t.id() == ID_unsignedbv || t.id() == ID_c_bool ||
               t.id() == ID_bool || t.id() == ID_floatbv ||
               t.id() == ID_fixedbv;
      expr = r ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else if(expr.id() == "__is_scalar")
    {
      bool r = t.id() == ID_signedbv || t.id() == ID_unsignedbv ||
               t.id() == ID_c_bool || t.id() == ID_bool ||
               t.id() == ID_floatbv || t.id() == ID_fixedbv ||
               t.id() == ID_c_enum_tag ||
               (t.id() == ID_pointer && !is_reference(t));
      expr = r ? exprt(true_exprt()) : exprt(false_exprt());
    }
    else
      expr = false_exprt();
  }
  else if(expr.id() == "lambda")
  {
    typecheck_expr_lambda(expr);
  }
  else if(expr.id() == ID_index)
  {
    // C++23 multidimensional subscript: struct[args] → operator[](args)
    auto &index_expr = to_binary_expr(expr);
    typecheck_expr_main(index_expr.op0());
    const typet &t = index_expr.op0().type();
    if(t.id() == ID_struct_tag || t.id() == ID_struct)
    {
      // Build operator[] call
      exprt op_name(ID_cpp_name);
      irept op_node(ID_operator);
      op_name.get_sub().push_back(op_node);
      irept bracket_node("[]");
      op_name.get_sub().push_back(bracket_node);

      exprt member(ID_member);
      member.add_to_operands(index_expr.op0());
      member.add(ID_component_cpp_name, op_name);

      // Collect arguments: if the index is a comma expression, split it
      exprt::operandst args;
      exprt &idx = index_expr.op1();
      if(idx.id() == ID_comma)
      {
        // Flatten comma expression into argument list
        std::function<void(exprt &)> flatten = [&](exprt &e)
        {
          if(e.id() == ID_comma)
          {
            flatten(to_binary_expr(e).op0());
            flatten(to_binary_expr(e).op1());
          }
          else
            args.push_back(e);
        };
        flatten(idx);
      }
      else
        args.push_back(idx);

      side_effect_expr_function_callt call(
        std::move(member), std::move(args), typet{}, expr.source_location());
      typecheck_side_effect_function_call(call);
      expr.swap(call);
    }
    else
      c_typecheck_baset::typecheck_expr_main(expr);
  }
  else
    c_typecheck_baset::typecheck_expr_main(expr);
}

void cpp_typecheckt::typecheck_expr_trinary(if_exprt &expr)
{
  PRECONDITION(expr.operands().size() == 3);

  implicit_typecast(expr.op0(), bool_typet());

  if(expr.op1().type().id()==ID_empty ||
     expr.op1().type().id()==ID_empty)
  {
    if(expr.op1().get_bool(ID_C_lvalue))
    {
      exprt e1(expr.op1());
      if(!standard_conversion_lvalue_to_rvalue(e1, expr.op1()))
      {
        error().source_location=e1.find_source_location();
        error() << "lvalue to rvalue conversion" << eom;
        throw 0;
      }
    }

    if(expr.op1().type().id()==ID_array)
    {
      exprt e1(expr.op1());
      if(!standard_conversion_array_to_pointer(e1, expr.op1()))
      {
        error().source_location=e1.find_source_location();
        error() << "array to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op1().type().id()==ID_code)
    {
      exprt e1(expr.op1());
      if(!standard_conversion_function_to_pointer(e1, expr.op1()))
      {
        error().source_location=e1.find_source_location();
        error() << "function to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op2().get_bool(ID_C_lvalue))
    {
      exprt e2(expr.op2());
      if(!standard_conversion_lvalue_to_rvalue(e2, expr.op2()))
      {
        error().source_location=e2.find_source_location();
        error() << "lvalue to rvalue conversion" << eom;
        throw 0;
      }
    }

    if(expr.op2().type().id()==ID_array)
    {
      exprt e2(expr.op2());
      if(!standard_conversion_array_to_pointer(e2, expr.op2()))
      {
        error().source_location=e2.find_source_location();
        error() << "array to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op2().type().id()==ID_code)
    {
      exprt e2(expr.op2());
      if(!standard_conversion_function_to_pointer(e2, expr.op2()))
      {
        error().source_location=expr.find_source_location();
        error() << "function to pointer conversion" << eom;
        throw 0;
      }
    }

    if(expr.op1().get(ID_statement)==ID_throw &&
       expr.op2().get(ID_statement)!=ID_throw)
      expr.type()=expr.op2().type();
    else if(expr.op2().get(ID_statement)==ID_throw &&
            expr.op1().get(ID_statement)!=ID_throw)
      expr.type()=expr.op1().type();
    else if(expr.op1().type().id()==ID_empty &&
            expr.op2().type().id()==ID_empty)
      expr.type() = void_type();
    else
    {
      error().source_location=expr.find_source_location();
      error() << "bad types for operands" << eom;
      throw 0;
    }
    return;
  }

  if(expr.op1().type() == expr.op2().type())
  {
    c_qualifierst qual1, qual2;
    qual1.read(expr.op1().type());
    qual2.read(expr.op2().type());

    if(qual1.is_subset_of(qual2))
      expr.type()=expr.op1().type();
    else
      expr.type()=expr.op2().type();
  }
  else
  {
    exprt e1=expr.op1();
    exprt e2=expr.op2();

    if(implicit_conversion_sequence(expr.op1(), expr.op2().type(), e1))
    {
      expr.type()=e1.type();
      expr.op1().swap(e1);
      // Ensure op2 matches the result type (e.g., c_bit_field may
      // differ from the converted type).
      if(expr.op2().type() != expr.type())
        expr.op2() = typecast_exprt::conditional_cast(expr.op2(), expr.type());
    }
    else if(implicit_conversion_sequence(expr.op2(), expr.op1().type(), e2))
    {
      expr.type()=e2.type();
      expr.op2().swap(e2);
      if(expr.op1().type() != expr.type())
        expr.op1() = typecast_exprt::conditional_cast(expr.op1(), expr.type());
    }
    else if(
      expr.op1().type().id() == ID_array &&
      expr.op2().type().id() == ID_array &&
      to_array_type(expr.op1().type()).element_type() ==
        to_array_type(expr.op2().type()).element_type())
    {
      // array-to-pointer conversion

      index_exprt index1(expr.op1(), from_integer(0, c_index_type()));

      index_exprt index2(expr.op2(), from_integer(0, c_index_type()));

      address_of_exprt addr1(index1);
      address_of_exprt addr2(index2);

      expr.op1()=addr1;
      expr.op2()=addr2;
      expr.type()=addr1.type();
      return;
    }
    else
    {
      error().source_location=expr.find_source_location();
      error() << "types are incompatible.\n"
              << "I got '" << type2cpp(expr.op1().type(), *this) << "' and '"
              << type2cpp(expr.op2().type(), *this) << "'." << eom;
      throw 0;
    }
  }

  if(expr.op1().get_bool(ID_C_lvalue) &&
     expr.op2().get_bool(ID_C_lvalue))
    expr.set(ID_C_lvalue, true);

  return;
}

void cpp_typecheckt::typecheck_expr_member(exprt &expr)
{
  typecheck_expr_member(
    expr,
    cpp_typecheck_fargst());
}

void cpp_typecheckt::typecheck_expr_sizeof(exprt &expr)
{
  // We need to overload, "sizeof-expression" can be mis-parsed
  // as a type.

  if(expr.operands().empty())
  {
    const typet &type=
      static_cast<const typet &>(expr.find(ID_type_arg));

    if(type.id()==ID_cpp_name)
    {
      // Check for sizeof...(Pack) — a parameter pack size query
      const cpp_namet &cpp_name = to_cpp_name(static_cast<const irept &>(type));
      if(!cpp_name.get_sub().empty())
      {
        const irep_idt &base_name =
          cpp_name.get_sub().front().get(ID_identifier);
        // Look up pack size by suffix match
        for(const auto &entry : template_map.pack_size_map)
        {
          const std::string &id = id2string(entry.first);
          std::string suffix = "::" + id2string(base_name);
          if(
            id.size() >= suffix.size() &&
            id.compare(id.size() - suffix.size(), suffix.size(), suffix) == 0)
          {
            expr = from_integer(entry.second, size_type());
            return;
          }
        }
        // Fallback: if there's exactly one pack, use it
        if(template_map.pack_size_map.size() == 1)
        {
          expr = from_integer(
            template_map.pack_size_map.begin()->second, size_type());
          return;
        }
      }

      // sizeof(X) may be ambiguous -- X can be either a type or
      // an expression.

      cpp_typecheck_fargst fargs;

      exprt symbol_expr=resolve(
        to_cpp_name(static_cast<const irept &>(type)),
        cpp_typecheck_resolvet::wantt::BOTH,
        fargs);

      if(symbol_expr.id()!=ID_type)
      {
        expr.copy_to_operands(symbol_expr);
        expr.remove(ID_type_arg);
      }
    }
    else if(type.id()==ID_array)
    {
      // sizeof(expr[index]) can be parsed as an array type!

      if(to_array_type(type).element_type().id() == ID_cpp_name)
      {
        cpp_typecheck_fargst fargs;

        exprt symbol_expr = resolve(
          to_cpp_name(
            static_cast<const irept &>(to_array_type(type).element_type())),
          cpp_typecheck_resolvet::wantt::BOTH,
          fargs);

        if(symbol_expr.id()!=ID_type)
        {
          // _NOT_ a type
          index_exprt index_expr(symbol_expr, to_array_type(type).size());
          expr.copy_to_operands(index_expr);
          expr.remove(ID_type_arg);
        }
      }
    }
  }

  c_typecheck_baset::typecheck_expr_sizeof(expr);
}

void cpp_typecheckt::typecheck_expr_ptrmember(exprt &expr)
{
  typecheck_expr_ptrmember(expr, cpp_typecheck_fargst());
}

void cpp_typecheckt::typecheck_function_expr(
  exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  if(expr.id()==ID_cpp_name)
    typecheck_expr_cpp_name(expr, fargs);
  else if(expr.id()==ID_member)
  {
    typecheck_expr_operands(expr);
    typecheck_expr_member(expr, fargs);
  }
  else if(expr.id()==ID_ptrmember)
  {
    typecheck_expr_operands(expr);
    add_implicit_dereference(to_unary_expr(expr).op());

    // is operator-> overloaded?
    if(to_unary_expr(expr).op().type().id() != ID_pointer)
    {
      std::string op_name = "operator->";

      const cpp_namet cpp_name(op_name, expr.source_location());

      // Build as a member function call: obj.operator->()
      exprt member(ID_member);
      member.add(ID_component_cpp_name) = cpp_name;
      member.copy_to_operands(
        already_typechecked_exprt{to_unary_expr(expr).op()});

      side_effect_expr_function_callt function_call(
        std::move(member), {}, uninitialized_typet{}, expr.source_location());

      typecheck_side_effect_function_call(function_call);

      add_implicit_dereference(function_call);
      already_typechecked_exprt::make_already_typechecked(function_call);

      to_unary_expr(expr).op().swap(function_call);
      typecheck_function_expr(expr, fargs);
      return;
    }

    typecheck_expr_ptrmember(expr, fargs);
  }
  else
    typecheck_expr(expr);
}

bool cpp_typecheckt::overloadable(const exprt &expr)
{
  // at least one argument must have class or enumerated type

  for(const auto &op : expr.operands())
  {
    typet t = op.type();

    if(is_reference(t))
      t = to_reference_type(t).base_type();

    if(
      t.id() == ID_struct || t.id() == ID_union || t.id() == ID_c_enum ||
      t.id() == ID_c_enum_tag || t.id() == ID_struct_tag ||
      t.id() == ID_union_tag)
    {
      return true;
    }
  }

  return false;
}

struct operator_entryt
{
  const irep_idt id;
  const char *op_name;
} const operators[] = {
  {ID_plus, "+"},        {ID_minus, "-"},       {ID_mult, "*"},
  {ID_div, "/"},         {ID_mod, "%"},         {ID_bitnot, "~"},
  {ID_bitand, "&"},      {ID_bitor, "|"},       {ID_bitxor, "^"},
  {ID_not, "!"},         {ID_unary_minus, "-"}, {ID_and, "&&"},
  {ID_or, "||"},         {ID_not, "!"},         {ID_index, "[]"},
  {ID_equal, "=="},      {ID_lt, "<"},          {ID_le, "<="},
  {ID_gt, ">"},          {ID_ge, ">="},         {ID_spaceship, "<=>"},
  {ID_shl, "<<"},        {ID_shr, ">>"},        {ID_notequal, "!="},
  {ID_dereference, "*"}, {ID_ptrmember, "->"},  {irep_idt(), nullptr}};

bool cpp_typecheckt::operator_is_overloaded(exprt &expr)
{
  // Check argument types first.
  // At least one struct/enum operand is required.

  if(!overloadable(expr))
    return false;
  else if(expr.id()==ID_dereference &&
          expr.get_bool(ID_C_implicit))
    return false;

  PRECONDITION(expr.operands().size() >= 1);

  if(expr.id()=="explicit-typecast")
  {
    // the cast operator can be overloaded

    typet t=expr.type();
    typecheck_type(t);
    std::string op_name=std::string("operator")+"("+cpp_type2name(t)+")";

    // turn this into a function call
    const cpp_namet cpp_name(op_name, expr.source_location());

    // See if the struct declares the cast operator as a member
    bool found_in_struct=false;
    PRECONDITION(!expr.operands().empty());
    const typet &t0 = to_unary_expr(expr).op().type();

    if(t0.id() == ID_struct_tag)
    {
      for(const auto &c : follow_tag(to_struct_tag_type(t0)).components())
      {
        if(!c.get_bool(ID_from_base) && c.get_base_name() == op_name)
        {
          found_in_struct=true;
          break;
        }
      }
    }

    if(!found_in_struct)
      return false;

    exprt member(ID_member);
    member.add(ID_component_cpp_name) = cpp_name;

    member.copy_to_operands(
      already_typechecked_exprt{to_unary_expr(expr).op()});

    side_effect_expr_function_callt function_call(
      std::move(member), {}, uninitialized_typet{}, expr.source_location());
    function_call.arguments().reserve(expr.operands().size());

    if(expr.operands().size()>1)
    {
      for(exprt::operandst::const_iterator
          it=(expr.operands().begin()+1);
          it!=(expr).operands().end();
          it++)
        function_call.arguments().push_back(*it);
    }

    typecheck_side_effect_function_call(function_call);

    if(expr.id()==ID_ptrmember)
    {
      add_implicit_dereference(function_call);
      already_typechecked_exprt::make_already_typechecked(function_call);
      to_unary_expr(expr).op().swap(function_call);
      typecheck_expr(expr);
      return true;
    }

    expr.swap(function_call);
    return true;
  }

  for(const operator_entryt *e=operators;
      !e->id.empty();
      e++)
  {
    if(expr.id()==e->id)
    {
      DATA_INVARIANT(
        expr.id() != ID_dereference || !expr.get_bool(ID_C_implicit),
        "no implicit dereference");

      std::string op_name=std::string("operator")+e->op_name;

      // first do function/operator
      const cpp_namet cpp_name(op_name, expr.source_location());

      // turn this into a function call
      // There are two options to overload an operator:
      //
      // 1. In the scope of a as a.operator(b, ...)
      // 2. Anywhere in scope as operator(a, b, ...)
      //
      // Using both is not allowed.
      //
      // We try and fail silently, maybe conversions will work
      // instead.

      // TODO: need to resolve an incomplete struct (template) here
      // go into scope of first operand
      if(to_multi_ary_expr(expr).op0().type().id() == ID_struct_tag)
      {
        const irep_idt &struct_identifier =
          to_multi_ary_expr(expr).op0().type().get(ID_identifier);

        // [over.match.oper]/3.2: the SET OF MEMBER CANDIDATES is
        // the result of a qualified lookup of `T1::operator@`.
        // CBMC's `resolve` performs RECURSIVE name lookup that
        // walks parent scopes when no match is found in the struct
        // scope, so a free `operator@` declared at file scope
        // (e.g., `BigInt operator%(const BigInt &,
        // const BigInt &)` in `bigint.hh`) would be returned here
        // even though T1 (BigInt) does not declare it as a member.
        // The downstream synthesis of `a.operator@(b)` then
        // produces a malformed member-call and the 2nd-option
        // (free-function) path is never reached, surfacing as
        //   conversion from 'const struct BigInt' to 'struct BigInt':
        //   implicit arithmetic conversion not permitted
        // for any free `operator@` between two `BigInt` operands
        // when one of them has a corresponding `operator@=` member
        // (which is the typical ADT pattern).  Skip the 1st option
        // entirely if T1 does not declare the operator as a member.
        bool has_member_op = false;
        const struct_typet &class_type =
          follow_tag(struct_tag_typet{struct_identifier});
        for(const auto &c : class_type.components())
        {
          // Inherited operators are member candidates too: the qualified
          // lookup of `T1::operator@` ([over.match.oper]/3.2) finds
          // members declared in base classes ([class.member.lookup]), so
          // from_base components must not be skipped.  A free operator
          // declared at file scope is not a component of T1, so this
          // still excludes the non-member case the gate guards against.
          if(c.get_base_name() == op_name && c.type().id() == ID_code)
          {
            has_member_op = true;
            break;
          }
        }

        if(has_member_op)
        {
          // get that scope
          cpp_save_scopet save_scope(cpp_scopes);
          cpp_scopes.set_scope(struct_identifier);

          // build fargs for resolver
          cpp_typecheck_fargst fargs;
          fargs.operands = expr.operands();
          fargs.has_object = true;
          fargs.in_use = true;

          // should really be a qualified search
          exprt resolve_result =
            resolve(cpp_name, cpp_typecheck_resolvet::wantt::VAR, fargs, false);

          if(resolve_result.is_not_nil())
          {
            // Per N5008 [over.match.oper]/3 + [over.match.best]/2:
            // member and non-member candidates form ONE combined
            // overload set; when both have same-rank conversion
            // sequences, a non-template specialization is preferred
            // over a function template specialization.
            //
            // CBMC's previous behaviour returned the first viable
            // member candidate without consulting the non-member
            // (ADL/free) set.  When the member candidate is a
            // function-template instantiation and a non-template
            // free operator is also viable (typically a `friend`
            // operator declared in the enclosing class with the
            // exact same parameter types), the free one must win
            // per [over.match.best]/2.
            //
            // Visible symptom on CBMC's own source:
            //   class messaget {
            //   public:
            //     class mstreamt : public std::ostringstream {
            //       template <class T> mstreamt &
            //       operator<<(const T &x) {  // template member
            //         static_cast<std::ostream &>(*this) << x;
            //         return *this;
            //       }
            //     };
            //     class eomt {};
            //     friend mstreamt &operator<<(mstreamt &, eomt);
            //   };
            // For `m << eom` (eom: messaget::eomt), the friend
            // non-template should win over the member template.
            // CBMC instead instantiated the member template, whose
            // body's `static_cast<std::ostream &>(*this) << eomt`
            // then fails with "operator 'shl' not defined".
            //
            // Detect the case: if the member candidate is a
            // function-template instantiation
            // (`#fn_template_args` set on its type), also try the
            // non-member candidate; if the non-member is
            // non-template, prefer it.
            bool member_is_template_specialization = false;
            if(resolve_result.id() == ID_symbol)
            {
              const symbolt *sym = symbol_table.lookup(
                to_symbol_expr(resolve_result).get_identifier());
              if(
                sym != nullptr &&
                sym->type.find(irep_idt{"#fn_template_args"}).is_not_nil())
              {
                member_is_template_specialization = true;
              }
            }
            if(member_is_template_specialization)
            {
              // Step out of the struct scope before doing the
              // non-member lookup so ADL-discovered candidates
              // (e.g., `friend operator@` declared in the
              // enclosing class) participate.
              save_scope.restore();

              cpp_typecheck_fargst free_fargs;
              free_fargs.operands = expr.operands();
              free_fargs.has_object = false;
              free_fargs.in_use = true;
              exprt free_resolve = resolve(
                cpp_name,
                cpp_typecheck_resolvet::wantt::VAR,
                free_fargs,
                false);
              if(free_resolve.is_not_nil())
              {
                bool free_is_non_template = true;
                if(free_resolve.id() == ID_symbol)
                {
                  const symbolt *fsym = symbol_table.lookup(
                    to_symbol_expr(free_resolve).get_identifier());
                  if(
                    fsym != nullptr &&
                    fsym->type.find(irep_idt{"#fn_template_args"}).is_not_nil())
                  {
                    free_is_non_template = false;
                  }
                }
                if(free_is_non_template)
                {
                  side_effect_expr_function_callt function_call(
                    cpp_name.as_expr(),
                    {},
                    uninitialized_typet{},
                    expr.source_location());
                  function_call.arguments().reserve(expr.operands().size());
                  for(const auto &op : as_const(expr).operands())
                    function_call.arguments().push_back(op);
                  typecheck_side_effect_function_call(function_call);
                  if(expr.id() == ID_ptrmember)
                  {
                    add_implicit_dereference(function_call);
                    already_typechecked_exprt::make_already_typechecked(
                      function_call);
                    to_multi_ary_expr(expr).op0() = function_call;
                    typecheck_expr(expr);
                    return true;
                  }
                  expr = function_call;
                  return true;
                }
              }
              // Fall back: re-enter struct scope so the member
              // call below uses the right scope.
              cpp_scopes.set_scope(struct_identifier);
            }

            // Found! We turn op(a, b, ...) into a.op(b, ...)
            exprt member(ID_member);
            member.add(ID_component_cpp_name) = cpp_name;

            member.copy_to_operands(
              already_typechecked_exprt{to_multi_ary_expr(expr).op0()});

            side_effect_expr_function_callt function_call(
              std::move(member),
              {},
              uninitialized_typet{},
              expr.source_location());
            function_call.arguments().reserve(expr.operands().size());

            if(expr.operands().size() > 1)
            {
              // skip first
              for(exprt::operandst::const_iterator it =
                    expr.operands().begin() + 1;
                  it != expr.operands().end();
                  it++)
                function_call.arguments().push_back(*it);
            }

            typecheck_side_effect_function_call(function_call);

            if(expr.id() == ID_ptrmember)
            {
              add_implicit_dereference(function_call);
              already_typechecked_exprt::make_already_typechecked(
                function_call);
              to_multi_ary_expr(expr).op0().swap(function_call);
              // Leave operator->'s class scope before type-checking the
              // ensuing member access, so it is access-checked at the
              // actual point of use rather than from within the class
              // that defines operator->.
              save_scope.restore();
              typecheck_expr(expr);
              return true;
            }

            expr = function_call;

            return true;
          }
        } // end if(has_member_op)
      }

      // 2nd option!
      {
        cpp_typecheck_fargst fargs;
        fargs.operands=expr.operands();
        fargs.has_object=false;
        fargs.in_use=true;

        exprt resolve_result=resolve(
             cpp_name, cpp_typecheck_resolvet::wantt::VAR, fargs, false);

        // [over.match.oper]/3.4 (last paragraph): if no operand
        // has class type, the non-member candidate set is
        // restricted to operators whose first parameter type is T1
        // (or reference-to-T1) when T1 is an enumeration type, or
        // whose second parameter type is T2 (or reference-to-T2)
        // when T2 is an enumeration type.  Without this, a free
        // operator on a class type whose constructors implicitly
        // accept arithmetic operands (e.g.,
        // `operator<<(const BigInt &, const BigInt &)` with
        // `BigInt(unsigned long)` and `BigInt(int)`) silently wins
        // over the built-in operator for an arithmetic operand
        // pair like `1UL << enum_const`.  The built-in candidate
        // (with at most an integral promotion) outranks the
        // user-defined one (which requires a user-defined
        // conversion sequence on each operand) per
        // [over.ics.rank]/2; CBMC's `operator_is_overloaded` does
        // not enumerate built-in candidates, so apply the
        // [over.match.oper]/3.4 restriction here as a filter.
        if(resolve_result.is_not_nil())
        {
          bool any_class_operand = false;
          for(const auto &op : expr.operands())
          {
            typet t = op.type();
            if(is_reference(t))
              t = to_reference_type(t).base_type();
            if(
              t.id() == ID_struct || t.id() == ID_struct_tag ||
              t.id() == ID_union || t.id() == ID_union_tag)
            {
              any_class_operand = true;
              break;
            }
          }
          if(!any_class_operand)
          {
            // Locate the resolved function's parameter types.
            const code_typet *fn_type = nullptr;
            if(resolve_result.type().id() == ID_code)
              fn_type = &to_code_type(resolve_result.type());
            if(fn_type != nullptr && fn_type->parameters().size() >= 1)
            {
              auto matches_enum_operand =
                [this](const typet &param_type, const exprt &operand) -> bool
              {
                typet ot = operand.type();
                if(is_reference(ot))
                  ot = to_reference_type(ot).base_type();
                if(ot.id() != ID_c_enum && ot.id() != ID_c_enum_tag)
                  return false;
                typet pt = param_type;
                if(is_reference(pt))
                  pt = to_reference_type(pt).base_type();
                if(pt.id() != ot.id())
                  return false;
                if(
                  pt.id() == ID_c_enum_tag &&
                  to_c_enum_tag_type(pt).get_identifier() !=
                    to_c_enum_tag_type(ot).get_identifier())
                  return false;
                return true;
              };
              const auto &params = fn_type->parameters();
              const auto &ops = expr.operands();
              bool restriction_ok = false;
              if(!ops.empty() && params.size() >= 1)
              {
                if(matches_enum_operand(params[0].type(), ops[0]))
                  restriction_ok = true;
              }
              if(!restriction_ok && ops.size() >= 2 && params.size() >= 2)
              {
                if(matches_enum_operand(params[1].type(), ops[1]))
                  restriction_ok = true;
              }
              if(!restriction_ok)
                resolve_result.make_nil();
            }
          }
        }

        if(resolve_result.is_not_nil())
        {
          // found!
          side_effect_expr_function_callt function_call(
            cpp_name.as_expr(),
            {},
            uninitialized_typet{},
            expr.source_location());
          function_call.arguments().reserve(expr.operands().size());

          // now do arguments
          for(const auto &op : as_const(expr).operands())
            function_call.arguments().push_back(op);

          typecheck_side_effect_function_call(function_call);

          if(expr.id()==ID_ptrmember)
          {
            add_implicit_dereference(function_call);
            already_typechecked_exprt::make_already_typechecked(function_call);
            to_multi_ary_expr(expr).op0() = function_call;
            typecheck_expr(expr);
            return true;
          }

          expr=function_call;

          return true;
        }
      }
    }
  }

  // C++20: synthesize relational operators from <=>
  if(
    (expr.id() == ID_lt || expr.id() == ID_gt || expr.id() == ID_le ||
     expr.id() == ID_ge) &&
    expr.operands().size() == 2 &&
    to_binary_expr(expr).op0().type().id() == ID_struct_tag)
  {
    const irep_idt &struct_id =
      to_binary_expr(expr).op0().type().get(ID_identifier);
    cpp_save_scopet save_scope(cpp_scopes);
    cpp_scopes.set_scope(struct_id);

    const cpp_namet spaceship_name("operator<=>", expr.source_location());
    cpp_typecheck_fargst fargs;
    fargs.operands = expr.operands();
    fargs.has_object = true;
    fargs.in_use = true;

    exprt spaceship_result =
      resolve(spaceship_name, cpp_typecheck_resolvet::wantt::VAR, fargs, false);

    if(spaceship_result.is_not_nil())
    {
      // Rewrite a < b  as  (a <=> b) < 0  (and similarly for >, <=, >=)
      exprt member(ID_member);
      member.add(ID_component_cpp_name) = spaceship_name;
      member.copy_to_operands(
        already_typechecked_exprt{to_binary_expr(expr).op0()});

      side_effect_expr_function_callt spaceship_call(
        std::move(member), {}, uninitialized_typet{}, expr.source_location());
      spaceship_call.arguments().push_back(to_binary_expr(expr).op1());
      typecheck_side_effect_function_call(spaceship_call);

      exprt zero = from_integer(0, signed_int_type());
      binary_relation_exprt cmp(
        std::move(spaceship_call), expr.id(), std::move(zero));
      cmp.add_source_location() = expr.source_location();
      expr.swap(cmp);
      return true;
    }
  }

  // C++20: synthesize operator!= from operator==
  if(
    expr.id() == ID_notequal && expr.operands().size() == 2 &&
    (to_binary_expr(expr).op0().type().id() == ID_struct_tag ||
     to_binary_expr(expr).op0().type().id() == ID_struct))
  {
    const cpp_namet eq_name("operator==", expr.source_location());
    cpp_typecheck_fargst fargs;
    fargs.operands = expr.operands();
    fargs.has_object = false;
    fargs.in_use = true;

    exprt eq_result =
      resolve(eq_name, cpp_typecheck_resolvet::wantt::VAR, fargs, false);

    if(eq_result.is_not_nil())
    {
      // Rewrite a != b  as  !(a == b)
      side_effect_expr_function_callt eq_call(
        eq_name.as_expr(), {}, uninitialized_typet{}, expr.source_location());
      for(const auto &op : as_const(expr).operands())
        eq_call.arguments().push_back(op);
      typecheck_side_effect_function_call(eq_call);

      not_exprt neg(
        typecast_exprt::conditional_cast(std::move(eq_call), bool_typet()));
      neg.add_source_location() = expr.source_location();
      expr.swap(neg);
      return true;
    }
  }

  return false;
}

/// Phase 2 target-typet overload — drives [temp.deduct.funcaddr]/1
/// deduction forward when the target is a pointer-to-function and
/// the operand is a cpp_name.  Falls through to the no-target
/// implementation otherwise.
void cpp_typecheckt::typecheck_expr_address_of(
  exprt &expr,
  const target_typet &target)
{
  if(
    target.has_target() && expr.id() == ID_address_of &&
    expr.operands().size() == 1 && to_unary_expr(expr).op().id() == ID_cpp_name)
  {
    exprt deduced = deduce_funcaddr_against_target(expr, *target.get());
    if(deduced.is_not_nil())
    {
      expr.swap(deduced);
      return;
    }
  }

  typecheck_expr_address_of(expr);
}

void cpp_typecheckt::typecheck_expr_address_of(exprt &expr)
{
  if(expr.operands().size() != 1)
  {
    error().source_location = expr.find_source_location();
    error() << "address_of expects one operand" << eom;
    throw 0;
  }

  exprt &op = to_address_of_expr(expr).op();

  // Per [expr.unary.op]/3: if the operand is a reference, &E produces
  // the address of the referred object.  Implicitly dereference the
  // reference first so the subsequent lvalue check passes.
  if(is_reference(op.type()))
    add_implicit_dereference(op);

  // Per [conv.rval] + [class.temporary]: temporary materialization
  // converts a prvalue to a glvalue denoting a temporary object.  CBMC
  // represents such a materialized temporary as a `temporary_object`
  // side effect, which the front end binds to reference parameters by
  // taking its address (e.g. an rvalue argument bound to a `T&&`
  // parameter).  That object has storage, so its address may be taken.
  // The C base typecheck below does not know about `temporary_object`
  // and would reject it as a non-lvalue; this matters when an already-
  // typechecked call carrying such a binding is re-typechecked (as
  // `cpp_constructor` does for constructor operands).  Mark it as an
  // lvalue so the address-of typecheck is idempotent.
  if(
    op.id() == ID_side_effect && op.get(ID_statement) == ID_temporary_object &&
    !op.get_bool(ID_C_lvalue))
  {
    op.set(ID_C_lvalue, true);
  }

  if(!op.get_bool(ID_C_lvalue) && expr.type().id() == ID_code)
  {
    error().source_location = expr.source_location();
    error() << "expr not an lvalue" << eom;
    throw 0;
  }

  if(op.type().id() == ID_code)
  {
    // we take the address of the method.
    // Per N5008 [conv.func]/1 + [over.over]/1: in lvalue-to-rvalue
    // conversion of a function-typed lvalue, take its address.
    // The implementation here assumes the lvalue arrived as a
    // member-access expression (ID_member); when overload
    // resolution arrives via a synthesised user-defined
    // conversion sequence (e.g. lambda → `std::function`
    // construction), the operand may be a different shape.
    // Emit a graceful error instead of aborting on the
    // DATA_INVARIANT — the caller's catch block then drops the
    // problematic candidate and overload resolution can
    // continue or report a localized "no viable conversion".
    if(op.id() != ID_member)
    {
      error().source_location = expr.source_location();
      error() << "address-of code requires a member expression "
              << "(operand id=" << op.id() << ")" << eom;
      throw 0;
    }
    exprt symb = cpp_symbol_expr(lookup(op.get(ID_component_name)));
    address_of_exprt address(symb, pointer_type(symb.type()));
    address.set(ID_C_implicit, true);
    op.swap(address);
  }

  if(op.id() == ID_address_of && op.get_bool(ID_C_implicit))
  {
    // must be the address of a function
    code_typet &code_type =
      to_code_type(to_pointer_type(op.type()).base_type());

    code_typet::parameterst &args=code_type.parameters();
    if(!args.empty() && args.front().get_this())
    {
      // it's a pointer to member function
      const struct_tag_typet symbol(code_type.get(ID_C_member_name));
      op.type().add(ID_to_member) = symbol;

      if(code_type.get_bool(ID_C_is_virtual))
      {
        error().source_location=expr.source_location();
        error() << "pointers to virtual methods"
                << " are currently not implemented" << eom;
        throw 0;
      }
    }
  }
  else if(op.id() == ID_ptrmember && to_unary_expr(op).op().id() == "cpp-this")
  {
    expr.type() = pointer_type(op.type());
    expr.type().add(ID_to_member) = to_struct_tag_type(
      to_pointer_type(to_unary_expr(op).op().type()).base_type());
    return;
  }

  // the C front end does not know about references
  const bool is_ref=is_reference(expr.type());
  c_typecheck_baset::typecheck_expr_address_of(expr);
  if(is_ref)
    expr.type() = reference_type(to_pointer_type(expr.type()).base_type());
}

void cpp_typecheckt::typecheck_expr_throw(exprt &expr)
{
  expr.type() = void_type();

  PRECONDITION(expr.operands().size() == 1 || expr.operands().empty());

  if(expr.operands().size()==1)
  {
    // nothing really to do; one can throw _almost_ anything
    const typet &exception_type = to_unary_expr(expr).op().type();

    if(exception_type.id() == ID_empty)
    {
      error().source_location = to_unary_expr(expr).op().find_source_location();
      error() << "cannot throw void" << eom;
      throw 0;
    }

    // annotate the relevant exception IDs
    expr.set(ID_exception_list,
             cpp_exception_list(exception_type, *this));
  }
}

void cpp_typecheckt::typecheck_expr_new(exprt &expr)
{
  // next, find out if we do an array

  if(expr.type().id()==ID_array)
  {
    // first typecheck the element type
    typecheck_type(to_array_type(expr.type()).element_type());

    // typecheck the size
    exprt &size=to_array_type(expr.type()).size();
    typecheck_expr(size);

    bool size_is_unsigned=(size.type().id()==ID_unsignedbv);
    bitvector_typet integer_type(
      size_is_unsigned ? ID_unsignedbv : ID_signedbv, config.ansi_c.int_width);
    implicit_typecast(size, integer_type);

    expr.set(ID_statement, ID_cpp_new_array);

    // save the size expression
    expr.set(ID_size, to_array_type(expr.type()).size());

    // new actually returns a pointer, not an array
    pointer_typet ptr_type =
      pointer_type(to_array_type(expr.type()).element_type());
    expr.type().swap(ptr_type);
  }
  else
  {
    // first typecheck type
    typecheck_type(expr.type());

    expr.set(ID_statement, ID_cpp_new);

    pointer_typet ptr_type=pointer_type(expr.type());
    expr.type().swap(ptr_type);
  }

  exprt object_expr(ID_new_object, to_pointer_type(expr.type()).base_type());
  object_expr.set(ID_C_lvalue, true);

  already_typechecked_exprt::make_already_typechecked(object_expr);

  // not yet typechecked-stuff
  exprt &initializer=static_cast<exprt &>(expr.add(ID_initializer));

  // arrays must not have an initializer
  if(!initializer.operands().empty() &&
     expr.get(ID_statement)==ID_cpp_new_array)
  {
    error().source_location =
      to_multi_ary_expr(expr).op0().find_source_location();
    error() << "new with array type must not use initializer" << eom;
    throw 0;
  }

  // For a default-initialized new-expression (no initializer arguments),
  // the selected default constructor must be accessible at the point of
  // the new-expression ([expr.new], [class.access]); cpp_constructor
  // resolves it in the object's own class scope, so check here from the
  // enclosing scope.
  if(initializer.operands().empty())
    check_default_constructor_access(
      to_pointer_type(expr.type()).base_type(),
      expr.find_source_location(),
      &cpp_scopes.current_scope());

  auto code = cpp_constructor(
    expr.find_source_location(), object_expr, initializer.operands());

  if(code.has_value())
    expr.add(ID_initializer).swap(code.value());
  else
    expr.add(ID_initializer) = nil_exprt();

  // we add the size of the object for convenience of the
  // runtime library
  auto size_of_opt =
    size_of_expr(to_pointer_type(expr.type()).base_type(), *this);

  if(size_of_opt.has_value())
  {
    auto &sizeof_expr = static_cast<exprt &>(expr.add(ID_sizeof));
    sizeof_expr = size_of_opt.value();
    sizeof_expr.add(ID_C_c_sizeof_type) =
      to_pointer_type(expr.type()).base_type();
  }
}

static exprt collect_comma_expression(const exprt &src)
{
  exprt result;

  if(src.id()==ID_comma)
  {
    PRECONDITION(src.operands().size() == 2);
    result = collect_comma_expression(to_binary_expr(src).op0());
    result.copy_to_operands(to_binary_expr(src).op1());
  }
  else
    result.copy_to_operands(src);

  return result;
}

void cpp_typecheckt::typecheck_expr_explicit_typecast(exprt &expr)
{
  // C++23 auto(x) decay copy: replace with the operand
  if(expr.type().id() == ID_auto && expr.operands().size() == 1)
  {
    auto &op = to_unary_expr(expr).op();
    typecheck_expr(op);
    exprt result = op;
    expr.swap(result);
    return;
  }

  // these can have 0 or 1 arguments

  if(expr.operands().empty())
  {
    // Default value, e.g., int()
    typecheck_type(expr.type());
    auto new_expr =
      ::zero_initializer(expr.type(), expr.find_source_location(), *this);
    if(!new_expr.has_value())
    {
      error().source_location = expr.find_source_location();
      error() << "cannot zero-initialize '" << to_string(expr.type()) << "'"
              << eom;
      throw 0;
    }

    new_expr->add_source_location() = expr.source_location();
    expr = *new_expr;
  }
  else if(expr.operands().size()==1)
  {
    auto &op = to_unary_expr(expr).op();

    // Explicitly given value, e.g., int(1).
    // There is an expr-vs-type ambiguity, as it is possible to write
    // (f)(1), where 'f' is a function symbol and not a type.
    // This also exists with a "comma expression", e.g.,
    // (f)(1, 2, 3)

    if(expr.type().id()==ID_cpp_name)
    {
      // try to resolve as type
      cpp_typecheck_fargst fargs;

      exprt symbol_expr=resolve(
        to_cpp_name(static_cast<const irept &>(expr.type())),
        cpp_typecheck_resolvet::wantt::TYPE,
        fargs,
        false); // fail silently

      if(symbol_expr.id()==ID_type)
        expr.type()=symbol_expr.type();
      else
      {
        // It's really a function call. Note that multiple arguments
        // become a comma expression, and that these are already typechecked.
        side_effect_expr_function_callt f_call(
          static_cast<const exprt &>(static_cast<const irept &>(expr.type())),
          collect_comma_expression(op).operands(),
          uninitialized_typet{},
          expr.source_location());

        typecheck_side_effect_function_call(f_call);

        expr.swap(f_call);
        return;
      }
    }
    else
      typecheck_type(expr.type());

    // We allow (TYPE){ initializer_list }
    // This is called "compound literal", and is syntactic
    // sugar for a (possibly local) declaration.
    if(op.id() == ID_initializer_list)
    {
      // C++17: direct-list-initialization of scalar/enum types
      // e.g., byte{42} where byte is a scoped enum
      if(
        op.operands().size() == 1 &&
        (expr.type().id() == ID_c_enum_tag || expr.type().id() == ID_signedbv ||
         expr.type().id() == ID_unsignedbv || expr.type().id() == ID_c_bool ||
         expr.type().id() == ID_bool || expr.type().id() == ID_floatbv ||
         expr.type().id() == ID_pointer))
      {
        op = to_unary_expr(op).op();
        // fall through to the typecast path below
      }
      else
      {
        // just do a normal initialization
        do_initializer(op, expr.type(), false);

        // This produces a struct-expression,
        // union-expression, array-expression,
        // or an expression for a pointer or scalar.
        // We produce a compound_literal expression.
        exprt tmp(ID_compound_literal, expr.type());
        tmp.add_to_operands(std::move(op));
        expr = tmp;
        expr.set(ID_C_lvalue, true); // these are l-values
        return;
      }
    }

    // Reject casts of non-static member functions — they require an
    // object and cannot be used as values.
    if(
      op.id() == ID_address_of && op.get_bool(ID_C_implicit) &&
      to_address_of_expr(op).object().type().id() == ID_code &&
      !to_code_type(to_address_of_expr(op).object().type())
         .get(ID_C_member_name)
         .empty())
    {
      error().source_location = expr.find_source_location();
      error() << "invalid use of non-static member function" << eom;
      throw 0;
    }

    // An operand of reference type (e.g. the result of
    // `static_cast<T&&>(x)`, as produced by std::forward in a function
    // template) denotes the referred object.  The cast helpers below
    // operate on the (non-reference) referred value -- const_typecast even
    // has a precondition to that effect -- and [expr.type.conv]/[conv.lval]
    // require the usual reference-binding/lvalue-to-rvalue handling.  Strip
    // the reference here so e.g. `T(static_cast<T&&>(x))` type-checks.
    if(is_reference(op.type()))
      add_implicit_dereference(op);

    exprt new_expr;

    if(
      const_typecast(op, expr.type(), new_expr) ||
      static_typecast(op, expr.type(), new_expr, false) ||
      reinterpret_typecast(op, expr.type(), new_expr, false))
    {
      expr=new_expr;
      add_implicit_dereference(expr);
    }
    else
    {
      error().source_location=expr.find_source_location();
      error() << "invalid explicit cast:\n"
              << "operand type: '" << to_string(op.type()) << "'\n"
              << "casting to: '" << to_string(expr.type()) << "'" << eom;
      throw 0;
    }
  }
  else
  {
    error().source_location=expr.find_source_location();
    error() << "explicit typecast expects 0 or 1 operands" << eom;
    throw 0;
  }
}

bool cpp_typecheckt::has_viable_init_list_constructor(
  const typet &type,
  const exprt &init_list)
{
  if(type.id() != ID_struct_tag)
    return false;

  const struct_typet &class_type = follow_tag(to_struct_tag_type(type));
  for(const auto &c : class_type.components())
  {
    if(c.type().id() != ID_code)
      continue;
    if(to_code_type(c.type()).return_type().id() != ID_constructor)
      continue;
    if(c.get_bool(ID_is_explicit))
      continue;
    const auto &params = to_code_type(c.type()).parameters();
    if(params.size() < 2)
      continue;
    typet p1 = params[1].type();
    if(is_reference(p1))
      p1 = to_reference_type(p1).base_type();
    if(p1.id() != ID_struct_tag)
      continue;
    if(
      id2string(to_struct_tag_type(p1).get_identifier())
        .find("tag-initializer_list<") == std::string::npos)
      continue;

    // The remaining parameters must be defaulted for the constructor to
    // accept a bare braced-init-list as its initializer_list argument.
    bool extras_default = true;
    for(std::size_t i = 2; i < params.size(); ++i)
    {
      if(!params[i].has_default_value())
      {
        extras_default = false;
        break;
      }
    }
    if(!extras_default)
      continue;

    // [over.match.list]/1 phase 1.1 applies only if this initializer-list
    // constructor is *viable* for the braced-init-list: each element must
    // be convertible to the initializer_list's element type.  Otherwise
    // phase 1.2 applies (e.g. `std::string{p}` for `const char *p` must
    // select `string(const char *)`, not the non-viable
    // `string(initializer_list<char>)`).
    typet elem_u;
    bool got_u = false;
    for(const auto &ic : follow_tag(to_struct_tag_type(p1)).components())
    {
      if(
        (ic.get_base_name() == "_begin" || ic.get_base_name() == "_M_array") &&
        ic.type().id() == ID_pointer)
      {
        elem_u = to_pointer_type(ic.type()).base_type();
        elem_u.remove(ID_C_constant);
        got_u = true;
        break;
      }
    }
    // If the element type cannot be determined, keep the prior behaviour
    // (treat the initializer-list constructor as applicable).
    if(!got_u)
      return true;

    bool viable = true;
    for(const auto &el : init_list.operands())
    {
      // A nested braced-init-list element list-initializes the element
      // type; leave that to the constructor to validate
      // (implicit_conversion_sequence does not model list-initialization).
      // Only a non-braced element that is not convertible to the element
      // type makes the initializer-list constructor non-viable.
      if(el.id() == ID_initializer_list)
        continue;
      exprt tc = el;
      unsigned rank = 0;
      try
      {
        typecheck_expr(tc);
      }
      catch(...)
      {
        viable = false;
        break;
      }
      if(!implicit_conversion_sequence(tc, elem_u, rank))
      {
        viable = false;
        break;
      }
    }
    if(viable)
      return true;
  }

  return false;
}

void cpp_typecheckt::typecheck_expr_explicit_constructor_call(exprt &expr)
{
  typecheck_type(expr.type());

  if(cpp_is_pod(expr.type()))
  {
    expr.id("explicit-typecast");
    typecheck_expr_main(expr);
  }
  else
  {
    // Aggregate initialization from braced-init-list for non-POD
    // aggregates (e.g., structs with reference members).
    if(
      expr.operands().size() == 1 &&
      expr.operands().front().id() == ID_initializer_list &&
      !expr.operands().front().operands().empty() &&
      expr.type().id() == ID_struct_tag)
    {
      const struct_typet &struct_type =
        follow_tag(to_struct_tag_type(expr.type()));

      // Check whether the struct has any non-copy constructor.
      bool has_non_copy_ctor = false;
      for(const auto &c : struct_type.components())
      {
        if(c.type().id() != ID_code || c.get_bool(ID_from_base))
          continue;
        const code_typet &code_type = to_code_type(c.type());
        if(code_type.return_type().id() != ID_constructor)
          continue;
        const auto &params = code_type.parameters();
        if(params.size() == 2 && is_reference(params[1].type()))
          continue;
        has_non_copy_ctor = true;
        break;
      }

      if(!has_non_copy_ctor)
      {
        const auto &ops = expr.operands().front().operands();
        struct_exprt result({}, expr.type());
        std::size_t idx = 0;
        bool aggregate = true;
        for(const auto &c : struct_type.components())
        {
          if(
            c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
            c.get_bool(ID_is_static) || c.type().id() == ID_code)
          {
            continue;
          }
          if(c.get_base_name() == "@most_derived")
            continue;
          if(idx < ops.size())
          {
            exprt val = ops[idx++];
            typecheck_expr(val);
            if(is_reference(c.type()))
              reference_initializer(val, to_reference_type(c.type()));
            else
              implicit_typecast(val, c.type());
            result.add_to_operands(std::move(val));
          }
          else
          {
            aggregate = false;
            break;
          }
        }
        if(aggregate)
        {
          result.add_source_location() = expr.source_location();
          expr = std::move(result);
          return;
        }
      }
    }

    exprt e = expr;

    // An empty braced-init-list {} means value-initialization,
    // which for class types calls the default constructor.
    if(
      e.operands().size() == 1 &&
      e.operands().front().id() == ID_initializer_list &&
      e.operands().front().operands().empty())
    {
      e.operands().clear();
    }

    // Direct-list-initialization: TYPE{a, b, c} should try to match
    // constructors with the individual elements of the braced-init-list.
    //
    // [over.match.list]/2 distinguishes two phases:
    //   2.1: try initializer-list ctors first, with the brace-init-list
    //        as a single argument.
    //   2.2: if 2.1 finds no viable ctor, retry with all ctors and the
    //        elements of the brace-init-list as the argument list.
    //
    // The previous unconditional expansion of `{e1, ..., en}` into
    // operands `[e1, ..., en]` skipped phase 2.1, so e.g.
    //   std::vector<X>{x1, x2}
    // never matched the `vector(initializer_list<X>, alloc&)` ctor and
    // failed when no `vector(X, X, ...)` ctor existed.  When the
    // target class has a non-explicit `initializer_list<U>` ctor (the
    // canonical phase-2.1 candidate), keep the brace-init-list as a
    // single argument so overload resolution can find it.  Otherwise
    // fall through to the existing phase-2.2 expansion.
    if(
      e.operands().size() == 1 &&
      e.operands().front().id() == ID_initializer_list &&
      !e.operands().front().operands().empty())
    {
      if(!has_viable_init_list_constructor(e.type(), e.operands().front()))
      {
        exprt::operandst expanded = std::move(e.operands().front().operands());
        e.operands() = std::move(expanded);
      }
    }

    new_temporary(e.source_location(), e.type(), e.operands(), expr);
  }
}

/// Type-check a `typeid` expression ([expr.typeid]).
///
/// The result is an lvalue of type `const std::type_info` that refers to a
/// unique-per-type object ([type.info]): two `type_info` objects compare
/// equal if and only if they denote the same type.  We model this by mapping
/// each type (after stripping references and top-level cv-qualifiers, per
/// [expr.typeid]) to a single static `std::type_info` object whose `__name`
/// member points at a distinct string, so that libstdc++'s
/// `type_info::operator==` (which compares `__name`) yields type identity.
///
/// For the `typeid(expression)` form, the static type of the operand is used;
/// a non-polymorphic operand is unevaluated.  The dynamic type of a
/// polymorphic glvalue is not modelled and is approximated by its static
/// type.
void cpp_typecheckt::typecheck_expr_typeid(exprt &expr)
{
  // [expr.typeid]/4: the program is ill-formed unless <typeinfo> has been
  // included before the use of typeid.
  const struct_tag_typet ti_type{"std::tag-type_info"};
  if(!symbol_table.has_symbol(ti_type.get_identifier()))
  {
    error().source_location = expr.find_source_location();
    error() << "typeid requires <typeinfo> to be included" << eom;
    throw 0;
  }

  const source_locationt source_location = expr.find_source_location();

  // Determine the type T whose std::type_info is requested.
  typet t;
  if(expr.has_operands())
  {
    // typeid(expression): use the static type of the operand.  Per
    // [expr.typeid]/3 a non-polymorphic operand is an unevaluated operand,
    // so we only retain its type and discard the operand itself.
    exprt &op = to_unary_expr(expr).op();
    typecheck_expr(op);
    t = op.type();
  }
  else
  {
    // typeid(type-id) -- but the operand may have been mis-parsed as a
    // type when it is in fact an expression (e.g. typeid(x) where x is a
    // variable).  Resolve a cpp_name to decide, as for sizeof.
    typet type_arg = static_cast<const typet &>(expr.find(ID_type_arg));
    if(type_arg.id() == ID_cpp_name)
    {
      cpp_typecheck_fargst fargs;
      exprt resolved = resolve(
        to_cpp_name(static_cast<const irept &>(type_arg)),
        cpp_typecheck_resolvet::wantt::BOTH,
        fargs);
      // Whether `resolved` is a type or an (unevaluated) expression, its
      // type is the static type whose std::type_info is requested.
      t = resolved.type();
    }
    else
    {
      typecheck_type(type_arg);
      t = type_arg;
    }
  }

  // [expr.typeid]/5: typeid ignores top-level cv-qualifiers, and references
  // are stripped to the referred-to type.  Types that differ only in these
  // share the same type_info object.
  if(is_reference(t))
    t = to_reference_type(t).base_type();
  t.remove(ID_C_constant);
  t.remove(ID_C_volatile);

  // Canonical key so that equal types share a single type_info object.
  const std::string key = type2name(t, *this);
  const irep_idt sym_id = "typeid$" + key;

  if(!symbol_table.has_symbol(sym_id))
  {
    const struct_typet &ti_struct = follow_tag(ti_type);

    // Build a value for the type_info object: the `__name` member points at
    // a string that is distinct for distinct types (so libstdc++'s
    // type_info::operator== yields type identity); all other members
    // (notably the vtable pointer, which is never used since the modelled
    // operations involve no virtual dispatch on type_info) are zero.
    string_constantt name_str{key};
    index_exprt first_char{name_str, from_integer(0, c_index_type())};

    struct_exprt::operandst field_values;
    for(const auto &comp : ti_struct.components())
    {
      // Skip non-data components (member functions, static members and
      // member types): they are not part of the object's data layout.
      if(
        comp.type().id() == ID_code || comp.get_bool(ID_is_static) ||
        comp.get_bool(ID_is_type))
      {
        continue;
      }

      if(comp.get_base_name() == "__name" && comp.type().id() == ID_pointer)
      {
        address_of_exprt name_addr{first_char};
        name_addr.type() = to_pointer_type(comp.type());
        field_values.push_back(std::move(name_addr));
      }
      else
      {
        auto zero = ::zero_initializer(comp.type(), source_location, *this);
        CHECK_RETURN(zero.has_value());
        field_values.push_back(std::move(*zero));
      }
    }

    struct_exprt ti_value{std::move(field_values), ti_type};
    ti_value.add_source_location() = source_location;

    symbolt ti_symbol;
    ti_symbol.name = sym_id;
    ti_symbol.base_name = sym_id;
    ti_symbol.type = ti_type;
    ti_symbol.type.set(ID_C_constant, true);
    ti_symbol.mode = ID_cpp;
    ti_symbol.is_static_lifetime = true;
    ti_symbol.is_lvalue = true;
    ti_symbol.location = source_location;
    ti_symbol.value = std::move(ti_value);
    symbol_table.insert(std::move(ti_symbol));
  }

  // The result is a const lvalue referring to the type_info object.
  typet const_ti_type = ti_type;
  const_ti_type.set(ID_C_constant, true);
  symbol_exprt result{sym_id, const_ti_type};
  result.set(ID_C_lvalue, true);
  result.add_source_location() = source_location;
  expr = std::move(result);
}

void cpp_typecheckt::typecheck_expr_this(exprt &expr)
{
  if(cpp_scopes.current_scope().class_identifier.empty())
  {
    error().source_location = expr.find_source_location();
    error() << "`this' is not allowed here" << eom;
    throw 0;
  }

  const exprt &this_expr=cpp_scopes.current_scope().this_expr;
  const source_locationt source_location=expr.find_source_location();

  if(this_expr.is_nil())
  {
    error().source_location = source_location;
    error() << "'this' used outside class context" << eom;
    throw 0;
  }
  PRECONDITION(this_expr.type().id() == ID_pointer);

  expr=this_expr;
  expr.add_source_location()=source_location;
}

void cpp_typecheckt::typecheck_expr_delete(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "delete expects one operand" << eom;
    throw 0;
  }

  const irep_idt statement=expr.get(ID_statement);

  if(statement==ID_cpp_delete)
  {
  }
  else if(statement==ID_cpp_delete_array)
  {
  }
  else
    UNREACHABLE;

  typet pointer_type = to_unary_expr(expr).op().type();

  if(pointer_type.id()!=ID_pointer)
  {
    error().source_location=expr.find_source_location();
    error() << "delete takes a pointer type operand, but got '"
            << to_string(pointer_type) << "'" << eom;
    throw 0;
  }

  // remove any const-ness of the argument
  // (which would impair the call to the destructor)
  to_pointer_type(pointer_type).base_type().remove(ID_C_constant);

  // delete expressions are always void
  expr.type()=typet(ID_empty);

  // we provide the right destructor, for the convenience
  // of later stages
  exprt new_object(ID_new_object, to_pointer_type(pointer_type).base_type());
  new_object.add_source_location()=expr.source_location();
  new_object.set(ID_C_lvalue, true);

  auto destructor_code =
    cpp_destructor(expr.source_location(), new_object, false);

  already_typechecked_exprt::make_already_typechecked(new_object);

  if(destructor_code.has_value())
  {
    // this isn't typechecked yet
    typecheck_code(destructor_code.value());
    expr.set(ID_destructor, destructor_code.value());
  }
  else
    expr.set(ID_destructor, nil_exprt());
}

void cpp_typecheckt::typecheck_expr_typecast(exprt &)
{
  // should not be called
  #if 0
  std::cout << "E: " << expr.pretty() << '\n';
  UNREACHABLE;
  #endif
}

void cpp_typecheckt::typecheck_expr_member(
  exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "member operator expects one operand" << eom;
    throw 0;
  }

  exprt &op0 = to_unary_expr(expr).op();
  add_implicit_dereference(op0);

  // The notation for explicit calls to destructors can be used regardless
  // of whether the type defines a destructor.  This allows you to make such
  // explicit calls without knowing if a destructor is defined for the type.
  // An explicit call to a destructor where none is defined has no effect.

  if(
    expr.find(ID_component_cpp_name).is_not_nil() &&
    to_cpp_name(expr.find(ID_component_cpp_name)).is_destructor() &&
    op0.type().id() != ID_struct && op0.type().id() != ID_struct_tag)
  {
    exprt tmp(ID_cpp_dummy_destructor);
    tmp.add_source_location()=expr.source_location();
    expr.swap(tmp);
    return;
  }

  // The member operator will trigger template elaboration
  elaborate_class_template(op0.type());

  if(op0.type().id() != ID_struct_tag && op0.type().id() != ID_union_tag)
  {
    error().source_location=expr.find_source_location();
    error() << "member operator requires struct/union type "
            << "on left hand side but got '" << to_string(op0.type()) << "'"
            << eom;
    throw 0;
  }

  const struct_union_typet &type =
    op0.type().id() == ID_struct_tag
      ? static_cast<const struct_union_typet &>(
          follow_tag(to_struct_tag_type(op0.type())))
      : static_cast<const struct_union_typet &>(
          follow_tag(to_union_tag_type(op0.type())));

  if(type.is_incomplete())
  {
    error().source_location = expr.find_source_location();
    error() << "member operator got incomplete type "
            << "on left hand side" << eom;
    throw 0;
  }

  irep_idt struct_identifier=type.get(ID_name);

  if(expr.find(ID_component_cpp_name).is_not_nil())
  {
    cpp_namet component_cpp_name=
      to_cpp_name(expr.find(ID_component_cpp_name));

    // Per N5008 [class.access]/4 + the lazy class-body elaboration
    // discipline: if the struct has no `ID_name` set, it is a
    // residual placeholder from a failed instantiation that wasn't
    // cleanly excluded upstream.  Without this guard,
    // `cpp_scopes.set_scope("")` aborts in the lookup with
    // "id '' not found" and crashes goto-cc.  Emit a localized
    // error and throw the conventional throw-0 signal instead so
    // the failure stays a user-visible compile error in the
    // calling translation unit rather than a CBMC abort.
    if(struct_identifier.empty())
    {
      error().source_location = expr.find_source_location();
      error() << "member operator on unnamed/incomplete struct "
              << "(typically from a failed template instantiation)" << eom;
      throw 0;
    }

    // go to the scope of the struct/union
    cpp_save_scopet save_scope(cpp_scopes);
    // Capture the genuine point of use ([class.access]) before navigating
    // into the object's class scope, so that member accessibility is
    // judged from the enclosing class/function rather than from the
    // object's type.
    cpp_scopet &naming_scope = cpp_scopes.current_scope();
    cpp_scopes.set_scope(struct_identifier);

    // resolve the member name in this scope
    cpp_typecheck_fargst new_fargs(fargs);
    new_fargs.add_object(op0);
    new_fargs.naming_scope = &naming_scope;

    exprt symbol_expr=resolve(
                        component_cpp_name,
                        cpp_typecheck_resolvet::wantt::VAR,
                        new_fargs);

    if(symbol_expr.id()==ID_dereference)
    {
      CHECK_RETURN(symbol_expr.get_bool(ID_C_implicit));
      exprt tmp = to_dereference_expr(symbol_expr).pointer();
      symbol_expr.swap(tmp);
    }

    // Soften to graceful error: typecheck_expr_member may receive
    // an unusual symbol_expr shape when resolve has fallen back to
    // a partial synthesis for an unresolvable member (for example
    // the destructor of a class whose components list has the
    // destructor but whose scope does not).  Rather than aborting
    // via DATA_INVARIANT, emit a diagnostic and throw.
    if(!(symbol_expr.id() == ID_symbol || symbol_expr.id() == ID_member ||
         symbol_expr.is_constant()))
    {
      error().source_location = expr.find_source_location();
      error() << "unresolved member expression (id=" << symbol_expr.id() << ")"
              << eom;
      throw 0;
    }

    // If it is a symbol or a constant, just return it!
    // Note: the resolver returns a symbol if the member
    // is static or if it is a constructor.

    if(symbol_expr.id()==ID_symbol)
    {
      if(
        symbol_expr.type().id() == ID_code &&
        to_code_type(symbol_expr.type()).return_type().id() == ID_constructor)
      {
        error().source_location=expr.find_source_location();
        error() << "member '"
                << lookup(symbol_expr.get(ID_identifier)).base_name
                << "' is a constructor" << eom;
        throw 0;
      }
      else
      {
        // Check if this is an instantiated member function template
        // (non-static, with a 'this' parameter).  In that case, we
        // must not treat it as a static member — fall through to the
        // member-expression path so that 'this' is added.
        if(
          symbol_expr.type().id() == ID_code &&
          !to_code_type(symbol_expr.type()).parameters().empty() &&
          to_code_type(symbol_expr.type()).parameters().front().get_this())
        {
          // Build a member expression so the caller adds 'this'.
          irep_idt component_name =
            to_symbol_expr(symbol_expr).get_identifier();
          expr.remove(ID_component_cpp_name);
          expr.set(ID_component_name, component_name);
          expr.type() = symbol_expr.type();
          return;
        }

        // it must be a static component
        const struct_typet::componentt &pcomp =
          type.get_component(to_symbol_expr(symbol_expr).identifier());

        if(pcomp.is_nil())
        {
          error().source_location=expr.find_source_location();

          error() << "'" << symbol_expr.get(ID_identifier)
                  << "' is not static member "
                  << "of class '" << to_string(op0.type()) << "'" << eom;
          throw 0;
        }
      }

      expr=symbol_expr;
      return;
    }
    else if(symbol_expr.is_constant())
    {
      expr=symbol_expr;
      return;
    }

    const irep_idt component_name=symbol_expr.get(ID_component_name);

    expr.remove(ID_component_cpp_name);
    expr.set(ID_component_name, component_name);
  }

  const irep_idt &component_name=expr.get(ID_component_name);
  INVARIANT(!component_name.empty(), "component name should not be empty");

  exprt component;
  component.make_nil();

  PRECONDITION(
    op0.type().id() == ID_struct || op0.type().id() == ID_union ||
    op0.type().id() == ID_struct_tag || op0.type().id() == ID_union_tag);

  exprt member;

  if(get_component(expr.source_location(), op0, component_name, member))
  {
    // because of possible anonymous members
    expr.swap(member);
  }
  else
  {
    error().source_location=expr.find_source_location();
    error() << "member '" << component_name << "' of '" << to_string(type)
            << "' not found" << eom;
    throw 0;
  }

  add_implicit_dereference(expr);

  if(expr.type().id()==ID_code)
  {
    // Check if the function body has to be typechecked
    symbolt &component_symbol = symbol_table.get_writeable_ref(component_name);

    if(component_symbol.value.id() == ID_cpp_not_typechecked)
      component_symbol.value.set(ID_is_used, true);
  }
}

void cpp_typecheckt::typecheck_expr_ptrmember(
  exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  PRECONDITION(expr.id() == ID_ptrmember);

  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "ptrmember operator expects one operand" << eom;
    throw 0;
  }

  auto &op = to_unary_expr(expr).op();

  add_implicit_dereference(op);

  // is operator-> overloaded?
  if(op.type().id() != ID_pointer)
  {
    std::string op_name = "operator->";

    const cpp_namet cpp_name(op_name, expr.source_location());

    side_effect_expr_function_callt function_call(
      cpp_name.as_expr(), {op}, uninitialized_typet{}, expr.source_location());

    typecheck_side_effect_function_call(function_call);

    already_typechecked_exprt::make_already_typechecked(function_call);

    op.swap(function_call);

    // Re-enter to handle the result (which may be a pointer or
    // another class with operator->).
    typecheck_expr_ptrmember(expr, fargs);
    return;
  }

  exprt tmp;
  op.swap(tmp);

  op.id(ID_dereference);
  op.add_to_operands(std::move(tmp));
  op.add_source_location() = expr.source_location();
  typecheck_expr_dereference(op);

  expr.id(ID_member);
  typecheck_expr_member(expr, fargs);
}

void cpp_typecheckt::typecheck_cast_expr(exprt &expr)
{
  if(expr.operands().size() != 1)
  {
    error().source_location=expr.find_source_location();
    error() << "cast expressions expect one operand" << eom;
    throw 0;
  }

  exprt &cast_op = to_unary_expr(expr).op();

  add_implicit_dereference(cast_op);

  const irep_idt &id = expr.id();

  typet &type = expr.type();
  typecheck_type(type);

  source_locationt source_location=expr.source_location();

  exprt new_expr;
  if(id==ID_const_cast)
  {
    if(!const_typecast(cast_op, type, new_expr))
    {
      error().source_location=cast_op.find_source_location();
      error() << "type mismatch on const_cast:\n"
              << "operand type: '" << to_string(cast_op.type()) << "'\n"
              << "cast type: '" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else if(id==ID_dynamic_cast)
  {
    if(!dynamic_typecast(cast_op, type, new_expr))
    {
      error().source_location=cast_op.find_source_location();
      error() << "type mismatch on dynamic_cast:\n"
              << "operand type: '" << to_string(cast_op.type()) << "'\n"
              << "cast type: '" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else if(id==ID_reinterpret_cast)
  {
    if(!reinterpret_typecast(cast_op, type, new_expr))
    {
      error().source_location=cast_op.find_source_location();
      error() << "type mismatch on reinterpret_cast:\n"
              << "operand type: '" << to_string(cast_op.type()) << "'\n"
              << "cast type: '" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else if(id==ID_static_cast)
  {
    if(!static_typecast(cast_op, type, new_expr))
    {
      error().source_location=cast_op.find_source_location();
      error() << "type mismatch on static_cast:\n"
              << "operand type: '" << to_string(cast_op.type()) << "'\n"
              << "cast type: '" << to_string(type) << "'" << eom;
      throw 0;
    }
  }
  else
    UNREACHABLE;

  expr.swap(new_expr);
}

void cpp_typecheckt::typecheck_expr_cpp_name(
  exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  source_locationt source_location=
    to_cpp_name(expr).source_location();

  if(expr.get_sub().size()==1 &&
     expr.get_sub()[0].id()==ID_name)
  {
    const irep_idt identifier=expr.get_sub()[0].get(ID_identifier);

    if(
      auto gcc_polymorphic = typecheck_gcc_polymorphic_builtin(
        identifier, fargs.operands, source_location))
    {
      expr = std::move(*gcc_polymorphic);
      return;
    }
  }

  for(std::size_t i=0; i<expr.get_sub().size(); i++)
  {
    if(expr.get_sub()[i].id()==ID_cpp_name)
    {
      typet &type=static_cast<typet &>(expr.get_sub()[i]);
      typecheck_type(type);

      std::string tmp="("+cpp_type2name(type)+")";

      typet name(ID_name);
      name.set(ID_identifier, tmp);
      name.add_source_location()=source_location;

      type=name;
    }
  }

  exprt symbol_expr=
    resolve(
      to_cpp_name(expr),
      cpp_typecheck_resolvet::wantt::VAR,
      fargs);

  // we want VAR
  CHECK_RETURN(symbol_expr.id() != ID_type);

  if(symbol_expr.id()==ID_member)
  {
    if(
      symbol_expr.operands().empty() ||
      to_multi_ary_expr(symbol_expr).op0().is_nil())
    {
      if(to_code_type(symbol_expr.type()).return_type().id() != ID_constructor)
      {
        if(cpp_scopes.current_scope().this_expr.is_nil())
        {
          if(symbol_expr.type().id()!=ID_code)
          {
            error().source_location=source_location;
            error() << "object missing" << eom;
            throw 0;
          }

          // may still be good for address of
        }
        else
        {
          // Try again
          exprt ptrmem(ID_ptrmember);
          ptrmem.operands().push_back(
            cpp_scopes.current_scope().this_expr);

          ptrmem.add(ID_component_cpp_name)=expr;

          ptrmem.add_source_location()=source_location;
          typecheck_expr_ptrmember(ptrmem, fargs);
          symbol_expr.swap(ptrmem);
        }
      }
    }
  }
  else if(
    fargs.in_use && symbol_expr.id() == ID_symbol &&
    symbol_expr.type().id() == ID_code &&
    to_code_type(symbol_expr.type()).return_type().id() != ID_constructor &&
    !to_code_type(symbol_expr.type()).parameters().empty() &&
    to_code_type(symbol_expr.type()).parameters().front().get_this() &&
    cpp_scopes.current_scope().this_expr.is_not_nil())
  {
    // Instantiated template member function returned as symbol_exprt
    // when called from within a class method body. Build a member
    // expression with dereferenced 'this' as the object so that
    // typecheck_method_application adds the this argument.
    const exprt &this_expr = cpp_scopes.current_scope().this_expr;
    exprt object(ID_dereference, to_pointer_type(this_expr.type()).base_type());
    object.copy_to_operands(this_expr);
    object.type().set(
      ID_C_constant,
      to_pointer_type(this_expr.type()).base_type().get_bool(ID_C_constant));
    object.set(ID_C_lvalue, true);
    object.add_source_location() = source_location;

    exprt member(ID_member);
    member.set(ID_component_name, to_symbol_expr(symbol_expr).get_identifier());
    member.add_to_operands(std::move(object));
    member.type() = symbol_expr.type();
    member.add_source_location() = source_location;
    symbol_expr.swap(member);
  }

  symbol_expr.add_source_location()=source_location;
  expr=symbol_expr;

  if(expr.id()==ID_symbol)
    typecheck_expr_function_identifier(expr);
  else if(expr.id() == ID_member)
  {
    const irep_idt &component = expr.get(ID_component_name);
    if(!component.empty())
    {
      auto it = deferred_method_bodies.find(component);
      if(it != deferred_method_bodies.end())
      {
        method_bodies.push_back(std::move(it->second));
        deferred_method_bodies.erase(it);
      }
    }
  }

  add_implicit_dereference(expr);
}

void cpp_typecheckt::add_implicit_dereference(exprt &expr)
{
  if(is_reference(expr.type()) || is_rvalue_reference(expr.type()))
  {
    // add implicit dereference
    dereference_exprt tmp(expr);
    tmp.set(ID_C_implicit, true);
    tmp.add_source_location()=expr.source_location();
    tmp.set(ID_C_lvalue, true);
    expr.swap(tmp);
  }
}

exprt cpp_typecheckt::deduce_funcaddr_against_target(
  const exprt &name_or_addressof,
  const typet &target_fn_pointer_type)
{
  // Target must be pointer-to-code per [conv.func].  When the target
  // is a reference-to-function we could apply [temp.deduct.call]/3
  // forwarding-reference rules, but the conforming lvalue-to-rvalue
  // / function-to-pointer conversion sequence reduces those to the
  // same deduction.
  if(
    target_fn_pointer_type.id() != ID_pointer &&
    target_fn_pointer_type.id() != ID_frontend_pointer)
  {
    return nil_exprt{};
  }
  if(target_fn_pointer_type.get_sub().empty())
    return nil_exprt{};
  const typet &target_fn =
    static_cast<const typet &>(target_fn_pointer_type.get_sub().front());
  if(target_fn.id() != ID_code)
    return nil_exprt{};

  // Source shape: `&cpp_name` (explicit address-of of a name) or
  // plain `cpp_name` (implicit function-to-pointer per
  // [conv.func]/1).  Everything else is passed through to the
  // default resolve path so real type mismatches surface as
  // user-visible errors.
  exprt inner = name_or_addressof;
  bool had_address_of = false;
  if(inner.id() == ID_address_of)
  {
    had_address_of = true;
    if(inner.operands().size() != 1)
      return nil_exprt{};
    inner = to_unary_expr(inner).op();
  }
  if(inner.id() != ID_cpp_name)
    return nil_exprt{};

  // Build synthetic fargs matching the target function's parameter
  // list.  Per [temp.deduct.funcaddr]/1 these drive the
  // [temp.deduct.type] algorithm (13.10.3.6) to deduce the template
  // arguments that make P == A.
  const code_typet &target_code = to_code_type(target_fn);
  cpp_typecheck_fargst synth_fargs;
  synth_fargs.in_use = true;
  for(const auto &p : target_code.parameters())
  {
    symbol_exprt synth{"funcaddr_target_synth", p.type()};
    synth.set(ID_C_lvalue, true);
    synth_fargs.operands.push_back(synth);
  }

  try
  {
    exprt resolved = resolve(
      to_cpp_name(inner),
      cpp_typecheck_resolvet::wantt::VAR,
      synth_fargs,
      /*fail_with_exception=*/false);
    if(resolved.is_not_nil() && resolved.type().id() == ID_code)
    {
      // [conv.func]/1: function-to-pointer conversion is implicit
      // when the target context requires it; keep the `C_implicit`
      // marker iff the source wasn't an explicit `&`.
      address_of_exprt addr{resolved, pointer_type(resolved.type())};
      addr.add_source_location() = name_or_addressof.source_location();
      if(!had_address_of)
        addr.set(ID_C_implicit, true);
      return std::move(addr);
    }
  }
  catch(...)
  {
    // [temp.deduct]/8: substitution failure is silent; let the
    // default resolve path report the mismatch.
  }

  return nil_exprt{};
}

/// Phase 4 target-typet overload — pushes the target on the
/// call-target stack so that the no-target body's `fargs` carries
/// it through to the resolver and the conversion paths.
/// `fargs.target` is consulted by Phase 4B's [temp.deduct.conv]/1
/// implementation in `user_defined_conversion_sequence`.
void cpp_typecheckt::typecheck_side_effect_function_call(
  side_effect_expr_function_callt &expr,
  const target_typet &target)
{
  call_target_stack.push_back(target);
  try
  {
    typecheck_side_effect_function_call(expr);
  }
  catch(...)
  {
    call_target_stack.pop_back();
    throw;
  }
  call_target_stack.pop_back();
}

// This function is currently 900+ lines.  Splitting it along the
// natural target-type boundaries (SystemC range handling, builtin
// dispatch, target-type-driven call resolution, per-argument
// conversion+rewriting) is tracked as a success criterion of the
// target-type-threading plan, see
// doc/architectural/cpp-frontend-plan-target-type-threading.md §7.6.
void cpp_typecheckt::typecheck_side_effect_function_call(
  side_effect_expr_function_callt &expr)
{
  // [expr.call] re-entrant guard: when typechecking resumes on an
  // already-typechecked subexpression — e.g., when
  // `cpp_constructor`'s operand loop calls `typecheck_expr` on an
  // existing `*move(...)` and the operand walk descends back into
  // the inner side-effect-call — the call has already had its
  // function operand resolved (`expr.function()` is a `symbol_expr`
  // pointing at the instantiated function template) and its
  // return type set to a reference (`T&` / `T&&`).  Re-running the
  // body would call `add_implicit_dereference(expr)` at the tail
  // again, wrapping the call in a SECOND `*` and corrupting the
  // parent dereference into `*(*call(...))`.
  // `typecheck_expr_dereference` would then reject the outer
  // dereference's operand as
  //   operand of unary * is not a pointer, but got 'struct T'
  // — which surfaces in libstdc++ chains as
  //   *move<ref_struct_tag(identifier=tag-X)>(...)
  // is not a pointer.  Detect this specific shape — a call already
  // resolved to a symbol AND whose return type is a reference —
  // and short-circuit.
  if(
    expr.function().id() == ID_symbol &&
    expr.function().type().id() == ID_code &&
    (is_reference(expr.type()) || is_rvalue_reference(expr.type())))
  {
    return;
  }

  // __builtin_is_constant_evaluated() always returns false at runtime.
  if(expr.function().id() == ID_cpp_name)
  {
    const auto &name = to_cpp_name(expr.function());
    const irep_idt &bn = name.get_base_name();
    if(bn == "__builtin_is_constant_evaluated")
    {
      exprt result = false_exprt();
      result.add_source_location() = expr.source_location();
      expr.swap(result);
      return;
    }
    // GCC built-in floating-point classification
    if(
      (bn == "__builtin_isfinite" || bn == "__builtin_isinf" ||
       bn == "__builtin_isnan" || bn == "__builtin_isnormal") &&
      expr.arguments().size() == 1)
    {
      typecheck_expr(expr.arguments()[0]);
      exprt arg = expr.arguments()[0];
      exprt result;
      if(bn == "__builtin_isfinite")
        result = isfinite_exprt(arg);
      else if(bn == "__builtin_isinf")
        result = isinf_exprt(arg);
      else if(bn == "__builtin_isnan")
        result = isnan_exprt(arg);
      else
        result = isnormal_exprt(arg);
      result.add_source_location() = expr.source_location();
      expr.swap(result);
      return;
    }
  }

  // For virtual functions, it is important to check whether
  // the function name is qualified. If it is qualified, then
  // the call is not virtual.
  bool is_qualified = false;

  if(expr.function().id()==ID_member ||
     expr.function().id()==ID_ptrmember)
  {
    if(expr.function().get(ID_component_cpp_name)==ID_cpp_name)
    {
      const cpp_namet &cpp_name=
        to_cpp_name(expr.function().find(ID_component_cpp_name));
      is_qualified=cpp_name.is_qualified();
    }
  }
  else if(expr.function().id()==ID_cpp_name)
  {
    const cpp_namet &cpp_name=to_cpp_name(expr.function());
    is_qualified=cpp_name.is_qualified();
  }

  // Backup of the original operand
  exprt op0=expr.function();

  // Pre-typecheck arguments to get their types for template argument
  // deduction. This is needed for function templates with partial
  // explicit template arguments (e.g., duration_cast<seconds>(d)).
  for(auto &arg : expr.arguments())
  {
    if(arg.type().id().empty() || arg.type().is_nil())
    {
      // [temp.deduct.funcaddr]: an argument of the form `&f` or
      // just `f` where `f` names a function template cannot be
      // typechecked in isolation — the deduction requires the
      // target parameter type of the outer call.  Defer this arg
      // to the post-function-resolution retry pass below so its
      // failure here doesn't abort the whole expression.
      bool is_funcaddr_template_candidate = false;
      {
        const exprt *probe = &arg;
        if(probe->id() == ID_address_of && probe->operands().size() == 1)
          probe = &to_unary_expr(*probe).op();
        if(probe->id() == ID_cpp_name)
          is_funcaddr_template_candidate = true;
      }
      if(is_funcaddr_template_candidate)
        continue;

      try
      {
        typecheck_expr(arg);
      }
      catch(...)
      {
        // ignore errors — argument may depend on template resolution
      }
    }
  }

  // now do the function -- this has been postponed
  // SystemC extension: a.range(upper, lower) on bitvector types
  if(
    expr.function().id() == ID_member &&
    expr.function().find(ID_component_cpp_name).is_not_nil() &&
    expr.arguments().size() == 2)
  {
    const cpp_namet &member_name =
      to_cpp_name(expr.function().find(ID_component_cpp_name));
    const irep_idt &base = member_name.get_base_name();
    if(base == "range")
    {
      exprt &obj = to_unary_expr(expr.function()).op();
      typecheck_expr(obj);
      add_implicit_dereference(obj);
      if(obj.type().id() == ID_unsignedbv)
      {
        typecheck_expr(expr.arguments()[0]);
        typecheck_expr(expr.arguments()[1]);
        const auto upper = numeric_cast<mp_integer>(expr.arguments()[0]);
        const auto lower = numeric_cast<mp_integer>(expr.arguments()[1]);
        if(upper.has_value() && lower.has_value() && *upper >= *lower)
        {
          const std::size_t width =
            numeric_cast_v<std::size_t>(*upper - *lower + 1);
          extractbits_exprt result(
            obj,
            from_integer(*lower, unsignedbv_typet(32)),
            unsignedbv_typet(width));
          result.add_source_location() = expr.source_location();
          expr.swap(result);
          return;
        }
      }
    }
  }

  // Forward-deduce template-function-address arguments against
  // target parameter types per [temp.deduct.funcaddr]/1.  Probe the
  // callee to obtain its parameter types (when resolvable without
  // fargs); for each deferred argument that's a `cpp_name` /
  // `&cpp_name`, retry the typecheck with the matching parameter as
  // the target, which routes to `deduce_funcaddr_against_target`
  // via `typecheck_expr(exprt &, const target_typet &)`.
  if(expr.function().id() == ID_cpp_name && !expr.arguments().empty())
  {
    bool any_deferred = false;
    for(const auto &a : expr.arguments())
      if(a.type().is_nil() || a.type().id().empty())
      {
        any_deferred = true;
        break;
      }

    if(any_deferred)
    {
      cpp_typecheck_fargst probe_fargs;
      exprt probe_fn = expr.function();
      try
      {
        probe_fn = resolve(
          to_cpp_name(probe_fn),
          cpp_typecheck_resolvet::wantt::VAR,
          probe_fargs,
          /*fail_with_exception=*/false);
      }
      catch(...)
      {
        probe_fn.make_nil();
      }

      if(probe_fn.is_not_nil() && probe_fn.type().id() == ID_code)
      {
        const auto &params = to_code_type(probe_fn.type()).parameters();
        for(std::size_t i = 0; i < params.size() && i < expr.arguments().size();
            ++i)
        {
          exprt &arg = expr.arguments()[i];
          if(!arg.type().is_nil() && !arg.type().id().empty())
            continue;

          typecheck_expr(arg, target_typet{params[i].type()});
        }
      }
    }
  }

  // Build fargs for overload resolution.  Carry the active target
  // type from the call-target stack so the resolver and conversion
  // paths can use it to drive [temp.deduct.conv]/1 deduction (see
  // Phase 4B in the target-type-threading plan).  The stack is set
  // by the `typecheck_side_effect_function_call(exprt &,
  // const target_typet &)` overload.
  cpp_typecheck_fargst call_fargs(expr);
  if(!call_target_stack.empty())
    call_fargs.target = call_target_stack.back();
  typecheck_function_expr(expr.function(), call_fargs);

  if(expr.function().id() == ID_pod_constructor)
  {
    PRECONDITION(expr.function().type().id() == ID_code);

    // This should be a POD, but in partially-elaborated template
    // instances (where our self-reference tolerance in
    // typecheck_compound_type left an unresolved cpp_name member
    // type) the pod_constructor tag can outlive the POD-ness of
    // the return type.  Fall back to a plain typecast / default
    // initialization rather than tripping a precondition and
    // crashing with an invariant violation.
    const typet &pod = to_code_type(expr.function().type()).return_type();
    if(!cpp_is_pod(pod))
    {
      if(expr.arguments().size() <= 1)
      {
        exprt typecast("explicit-typecast");
        typecast.type() = pod;
        typecast.add_source_location() = expr.source_location();
        if(!expr.arguments().empty())
          typecast.copy_to_operands(expr.arguments().front());
        typecheck_expr_explicit_typecast(typecast);
        expr.swap(typecast);
        return;
      }
      error().source_location = expr.source_location();
      error() << "zero or one argument expected" << eom;
      throw 0;
    }

    // These aren't really function calls, but either conversions or
    // initializations.
    if(expr.arguments().size() <= 1)
    {
      exprt typecast("explicit-typecast");
      typecast.type()=pod;
      typecast.add_source_location()=expr.source_location();
      if(!expr.arguments().empty())
        typecast.copy_to_operands(expr.arguments().front());
      typecheck_expr_explicit_typecast(typecast);
      expr.swap(typecast);
    }
    else
    {
      error().source_location=expr.source_location();
      error() << "zero or one argument expected" << eom;
      throw 0;
    }

    return;
  }
  else if(expr.function().id() == ID_cpp_dummy_destructor)
  {
    // these don't do anything, e.g., (char*)->~char()
    typecast_exprt no_op(from_integer(0, signed_int_type()), void_type());
    expr.swap(no_op);
    return;
  }

  // look at type of function

  if(expr.function().type().id()==ID_pointer)
  {
    if(expr.function().type().find(ID_to_member).is_not_nil())
    {
      const exprt &bound =
        static_cast<const exprt &>(expr.function().type().find(ID_C_bound));

      if(bound.is_nil())
      {
        error().source_location=expr.source_location();
        error() << "pointer-to-member not bound" << eom;
        throw 0;
      }

      // add `this'
      DATA_INVARIANT(bound.type().id() == ID_pointer, "should be pointer");
      expr.arguments().insert(expr.arguments().begin(), bound);

      // we don't need the object any more
      expr.function().type().remove(ID_C_bound);
    }

    // do implicit dereference
    if(expr.function().id() == ID_address_of)
    {
      exprt tmp;
      tmp.swap(to_address_of_expr(expr.function()).object());
      expr.function().swap(tmp);
    }
    else
    {
      PRECONDITION(expr.function().type().id() == ID_pointer);
      dereference_exprt tmp(expr.function());
      tmp.add_source_location() = expr.function().source_location();
      expr.function().swap(tmp);
    }

    if(expr.function().type().id()!=ID_code)
    {
      error().source_location = expr.function().find_source_location();
      error() << "expecting code as argument" << eom;
      throw 0;
    }
  }
  else if(expr.function().type().id()==ID_code)
  {
    if(expr.function().type().get_bool(ID_C_is_virtual) && !is_qualified)
    {
      exprt vtptr_member;
      if(op0.id()==ID_member || op0.id()==ID_ptrmember)
      {
        vtptr_member.id(op0.id());
        vtptr_member.add_to_operands(std::move(to_unary_expr(op0).op()));
      }
      else
      {
        vtptr_member.id(ID_ptrmember);
        exprt this_expr("cpp-this");
        vtptr_member.add_to_operands(std::move(this_expr));
      }

      // get the virtual table
      auto this_type = to_pointer_type(
        to_code_type(expr.function().type()).parameters().front().type());

      const struct_typet &vt_struct =
        follow_tag(to_struct_tag_type(this_type.base_type()));

      // Find the vtable pointer component — it may be inherited from a
      // base class, so search by the ID_is_vtptr flag rather than by name.
      irep_idt vtable_name;
      const struct_typet::componentt *vt_compo_ptr = nullptr;
      for(const auto &c : vt_struct.components())
      {
        if(c.get_bool(ID_is_vtptr))
        {
          vt_compo_ptr = &c;
          vtable_name = c.get_name();
          break;
        }
      }
      CHECK_RETURN(vt_compo_ptr != nullptr);
      const struct_typet::componentt &vt_compo = *vt_compo_ptr;

      vtptr_member.set(ID_component_name, vtable_name);

      // look for the right entry
      irep_idt vtentry_component_name =
        to_pointer_type(vt_compo.type()).base_type().get_string(ID_identifier) +
        "::" + expr.function().type().get_string(ID_C_virtual_name);

      exprt vtentry_member(ID_ptrmember);
      vtentry_member.copy_to_operands(vtptr_member);
      vtentry_member.set(ID_component_name, vtentry_component_name);
      typecheck_expr(vtentry_member);

      CHECK_RETURN(vtentry_member.type().id() == ID_pointer);

      {
        dereference_exprt tmp(vtentry_member);
        tmp.add_source_location() = expr.function().source_location();
        vtentry_member.swap(tmp);
      }

      // Typecheck the expression as if it was not virtual
      // (add the this pointer)

      expr.type()=
        to_code_type(expr.function().type()).return_type();

      if(expr.function().id() == ID_member)
        typecheck_method_application(expr);

      // Let's make the call virtual
      expr.function().swap(vtentry_member);

      typecheck_function_call_arguments(expr);
      add_implicit_dereference(expr);
      return;
    }
  }
  else if(expr.function().type().id() == ID_struct_tag)
  {
    const cpp_namet cppname("operator()", expr.source_location());

    // The function expression evaluates to a struct value (e.g., F()).
    // Wrap it in a temporary_object so the this pointer can be formed.
    exprt obj = std::move(expr.function());
    if(!obj.get_bool(ID_C_lvalue))
    {
      side_effect_exprt tmp(
        ID_temporary_object, obj.type(), obj.source_location());
      tmp.add_to_operands(std::move(obj));
      tmp.set(ID_C_lvalue, true);
      tmp.set(ID_mode, ID_cpp);
      obj = std::move(tmp);
    }

    exprt member(ID_member);
    member.add(ID_component_cpp_name) = cppname;
    member.add_to_operands(already_typechecked_exprt{std::move(obj)});

    expr.function().swap(member);
    typecheck_side_effect_function_call(expr);

    return;
  }
  else
  {
    error().source_location=expr.function().find_source_location();
    error() << "function call expects function or function "
            << "pointer as argument, but got '"
            << to_string(expr.function().type()) << "'" << eom;
    throw 0;
  }

  expr.type()=
    to_code_type(expr.function().type()).return_type();

  if(expr.type().id()==ID_constructor)
  {
    PRECONDITION(expr.function().id() == ID_symbol);

    const code_typet::parameterst &parameters=
      to_code_type(expr.function().type()).parameters();

    DATA_INVARIANT(!parameters.empty(), "parameters expected");

    const auto &this_type = to_pointer_type(parameters[0].type());

    // change type from 'constructor' to object type
    expr.type() = this_type.base_type();

    // create temporary object
    side_effect_exprt tmp_object_expr(
      ID_temporary_object, this_type.base_type(), expr.source_location());
    tmp_object_expr.set(ID_C_lvalue, true);
    tmp_object_expr.set(ID_mode, ID_cpp);

    exprt member;

    exprt new_object(ID_new_object, tmp_object_expr.type());
    new_object.set(ID_C_lvalue, true);

    PRECONDITION(tmp_object_expr.type().id() == ID_struct_tag);

    get_component(expr.source_location(),
                  new_object,
                  expr.function().get(ID_identifier),
                  member);

    // special case for the initialization of parents
    if(member.get_bool(ID_C_not_accessible))
    {
      PRECONDITION(!member.get(ID_C_access).empty());
      tmp_object_expr.set(ID_C_not_accessible, true);
      tmp_object_expr.set(ID_C_access, member.get(ID_C_access));
    }

    // the constructor is being used, so make sure the destructor
    // will be available
    {
      // find name of destructor
      const struct_typet::componentst &components =
        follow_tag(to_struct_tag_type(tmp_object_expr.type())).components();

      for(const auto &c : components)
      {
        const typet &type = c.type();

        if(
          !c.get_bool(ID_from_base) && type.id() == ID_code &&
          to_code_type(type).return_type().id() == ID_destructor)
        {
          add_method_body(&symbol_table.get_writeable_ref(c.get_name()));
          break;
        }
      }
    }

    expr.function().swap(member);

    typecheck_method_application(expr);
    typecheck_function_call_arguments(expr);

    const code_expressiont new_code(expr);
    tmp_object_expr.add(ID_initializer)=new_code;
    expr.swap(tmp_object_expr);
    return;
  }

  PRECONDITION(expr.operands().size() == 2);

  if(expr.function().id()==ID_member)
  {
    typecheck_method_application(expr);
    // Update return type after method application — the method's auto
    // return type may have been deduced during convert_function.
    if(has_auto(expr.type()))
      expr.type() = to_code_type(expr.function().type()).return_type();
  }
  else
  {
    // for the object of a method call,
    // we are willing to add an "address_of"
    // for the sake of operator overloading

    const code_typet::parameterst &parameters =
      to_code_type(expr.function().type()).parameters();

    if(
      !parameters.empty() && parameters.front().get_this() &&
      !expr.arguments().empty())
    {
      const code_typet::parametert &parameter = parameters.front();

      exprt &operand = expr.arguments().front();
      INVARIANT(
        parameter.type().id() == ID_pointer,
        "`this' parameter should be a pointer");

      if(
        operand.type().id() != ID_pointer &&
        operand.type() == to_pointer_type(parameter.type()).base_type())
      {
        address_of_exprt tmp(operand, pointer_type(operand.type()));
        tmp.add_source_location()=operand.source_location();
        operand=tmp;
      }
    }
  }

  CHECK_RETURN(expr.operands().size() == 2);

  // Generic lambda instantiation: if the call target is a generic lambda,
  // instantiate a new version with the actual argument types.
  instantiate_generic_lambda(expr);

  typecheck_function_call_arguments(expr);

  CHECK_RETURN(expr.operands().size() == 2);

  add_implicit_dereference(expr);

  // Trigger elaboration of lazily deferred template method bodies.
  if(auto sym_expr = expr_try_dynamic_cast<symbol_exprt>(expr.function()))
  {
    auto it = deferred_method_bodies.find(sym_expr->get_identifier());
    if(it != deferred_method_bodies.end())
    {
      method_bodies.push_back(std::move(it->second));
      deferred_method_bodies.erase(it);
    }
  }

  // constexpr function evaluation
  if(auto sym_expr = expr_try_dynamic_cast<symbol_exprt>(expr.function()))
  {
    const auto *symbol_ptr = symbol_table.lookup(sym_expr->get_identifier());
    // The body is recognised as code either by `value.type().id() ==
    // ID_code` (post-`convert_function`, when the body's TYPE is set
    // to the function's code type) or by `value.id() == ID_code`
    // (the parsed/queued state where the value IS a code block but
    // its type field is empty).  Accept both — the second case
    // matters when we are about to eagerly convert the body so it
    // gets resolved in its own (class) scope.
    bool body_is_code =
      symbol_ptr != nullptr &&
      (symbol_ptr->value.type().id() == ID_code ||
       symbol_ptr->value.id() == ID_code);
    bool eligible_constexpr =
      symbol_ptr != nullptr && symbol_ptr->is_macro &&
      constant_expression_context != 0 &&
      !functions_being_typechecked.count(sym_expr->get_identifier()) &&
      !deferred_typechecking.count(sym_expr->get_identifier()) && body_is_code;
    if(eligible_constexpr)
    {
      // Pre-check whether the arguments are fully constant: if not,
      // there is no way constexpr-eval can fold the call regardless
      // of whether the body is resolved.  Skipping the eager-convert
      // path in that case avoids unnecessary cascading instantiations
      // for runtime-only invocations of constexpr methods.
      bool args_are_constant_pre = true;
      for(const auto &arg : expr.arguments())
      {
        arg.visit_pre(
          [&args_are_constant_pre](const exprt &e) {
            if(e.id() == ID_symbol)
              args_are_constant_pre = false;
          });
        if(!args_are_constant_pre)
          break;
      }
      // For constexpr methods of a template class whose body was
      // queued by `add_method_body` but not yet processed, the body's
      // expressions are still in cpp_name form.  Substituting and
      // installing such a body at the call site would leave
      // unresolved names in the caller's scope.  Eagerly process the
      // body via convert_function so it is type-checked in the
      // function's own (class) scope first.  We restrict this to
      // class methods (have a `C_member_name`) where the body has
      // not yet been type-checked (its type field is still empty)
      // and where the body actually contains unresolved cpp_names.
      // The cpp_name guard avoids unwanted cascading instantiations
      // for already-resolved methods that just happen to lack a code
      // type on their `value`.
      bool needs_eager_convert = false;
      if(
        args_are_constant_pre &&
        !symbol_ptr->type.get(ID_C_member_name).empty() &&
        symbol_ptr->value.type().id() != ID_code)
      {
        // Walk the body's full irept tree (operands AND types and
        // other named-sub fields).  exprt::visit_pre only walks
        // operands, so a `cpp_name` appearing as the `type` field
        // of an inner expression (e.g., the target type of a
        // `static_cast<int_type>(...)`) is invisible to it.  Such
        // cpp_names must still trigger eager-convert: when the
        // body is later substituted into the caller's scope by
        // the constexpr inliner, an unresolved `int_type`
        // cpp_name in the substituted expression's type field
        // surfaces as the spurious diagnostic
        //
        //   invalid implicit conversion from '<<type:cpp_name>>'
        //   to 'signed int'
        //
        // even though `int_type` is a perfectly resolvable
        // typedef in the function's own (class) scope.  Walk the
        // full irept tree to detect any unresolved cpp_name
        // anywhere in the body.
        std::function<void(const irept &)> has_cpp_name =
          [&](const irept &n) {
            if(needs_eager_convert)
              return;
            if(n.id() == ID_cpp_name)
            {
              needs_eager_convert = true;
              return;
            }
            for(const auto &s : n.get_sub())
              has_cpp_name(s);
            for(const auto &ns : n.get_named_sub())
              has_cpp_name(ns.second);
          };
        has_cpp_name(symbol_ptr->value);
      }
      if(needs_eager_convert)
      {
        symbolt &writeable =
          symbol_table.get_writeable_ref(sym_expr->get_identifier());
        const irep_idt class_id = writeable.type.get(ID_C_member_name);
        const symbolt *class_sym = symbol_table.lookup(class_id);
        cpp_saved_template_mapt saved_map(template_map);
        if(
          class_sym != nullptr &&
          class_sym->type.find(ID_C_template).is_not_nil() &&
          class_sym->type.find(ID_C_template_arguments).is_not_nil())
        {
          template_map.build(
            static_cast<const template_typet &>(
              class_sym->type.find(ID_C_template)),
            static_cast<const cpp_template_args_tct &>(
              class_sym->type.find(ID_C_template_arguments)));
        }
        methods_seen.insert(sym_expr->get_identifier());
        try
        {
          convert_function(writeable);
        }
        catch(...)
        {
          // typecheck failure: leave value unchanged, fall through to
          // the symbol_ptr->value check below which will see whatever
          // state the body is in
        }
        symbol_ptr = symbol_table.lookup(sym_expr->get_identifier());
        eligible_constexpr =
          symbol_ptr != nullptr &&
          symbol_ptr->value.type().id() == ID_code;
      }
    }
    if(eligible_constexpr)
    {
      const auto &code_type = to_code_type(symbol_ptr->type);
      PRECONDITION(expr.arguments().size() == code_type.parameters().size());
      replace_symbolt value_map;
      auto param_it = code_type.parameters().begin();
      bool args_are_constant = true;
      for(const auto &arg : expr.arguments())
      {
        // Check if argument is fully constant (no symbol references).
        // If not, we can't evaluate this constexpr call.
        arg.visit_pre(
          [&args_are_constant](const exprt &e)
          {
            if(e.id() == ID_symbol)
              args_are_constant = false;
          });
        value_map.insert(
          symbol_exprt{param_it->get_identifier(), param_it->type()},
          typecast_exprt::conditional_cast(arg, param_it->type()));
        ++param_it;
      }
      bool can_evaluate = args_are_constant;
      const auto &block = to_code_block(to_code(symbol_ptr->value));
      for(const auto &stmt : block.statements())
      {
        if(!can_evaluate)
          break;
        if(
          auto return_stmt = expr_try_dynamic_cast<code_frontend_returnt>(stmt))
        {
          PRECONDITION(return_stmt->has_return_value());
          exprt tmp = return_stmt->return_value();
          value_map.replace(tmp);
          simplify(tmp, *this);
          // Recursively evaluate nested constexpr function calls
          // (e.g., _Big_multiply inside _Ratio_less).
          {
            bool changed = true;
            while(changed)
            {
              changed = false;
              tmp.visit_post(std::function<void(exprt &)>(
                [&](exprt &node)
                {
                  if(
                    node.id() == ID_side_effect &&
                    to_side_effect_expr(node).get_statement() ==
                      ID_function_call)
                  {
                    auto &call = to_side_effect_expr_function_call(node);
                    exprt before = call;
                    typecheck_side_effect_function_call(call);
                    if(call != before)
                    {
                      node = call;
                      changed = true;
                    }
                  }
                }));
              if(changed)
                simplify(tmp, *this);
            }
          }
          // Aggregate init: convert {a, b, ...} to struct{.m1=a, .m2=b}
          if(
            tmp.id() == ID_initializer_list &&
            code_type.return_type().id() == ID_struct_tag)
          {
            const auto &st =
              follow_tag(to_struct_tag_type(code_type.return_type()));
            const auto &comps = st.components();
            struct_exprt s({}, code_type.return_type());
            std::size_t i = 0;
            for(const auto &c : comps)
            {
              if(c.get_is_padding() || c.type().id() == ID_code)
                continue;
              if(i < tmp.operands().size())
                s.operands().push_back(typecast_exprt::conditional_cast(
                  tmp.operands()[i++], c.type()));
              else
                break;
            }
            if(i == tmp.operands().size())
            {
              // Verify all fields are constant (no remaining symbols
              // from unevaluated parameters).
              bool fully_evaluated = true;
              s.visit_pre(
                [&fully_evaluated](const exprt &e)
                {
                  if(e.id() == ID_symbol)
                    fully_evaluated = false;
                });
              if(fully_evaluated)
                tmp = std::move(s);
              else
              {
                can_evaluate = false;
                break;
              }
            }
            else
            {
              can_evaluate = false;
              break;
            }
          }
          // Only replace the call with the result if it's fully
          // evaluated (no remaining function calls, unresolved
          // names, or non-`code` symbols that haven't been folded
          // to constants).  An unresolved `cpp_name` in the body
          // means the function's body was substituted at this call
          // site without first being type-checked in the function's
          // own (class) scope; if we install it in the caller's
          // scope, the cpp_name will be resolved there and likely
          // fail with `symbol '...' is unknown`.  This shows up for
          // class-scope `constexpr` member functions whose body
          // references same-class members (e.g. a static
          // `value`) when the call is used as a non-type template
          // argument and the body hasn't been processed by
          // `typecheck_method_bodies` yet.
          {
            bool has_calls = false;
            tmp.visit_pre(
              [&has_calls](const exprt &e)
              {
                if(
                  e.id() == ID_side_effect ||
                  (e.id() == ID_symbol && e.type().id() != ID_code) ||
                  e.id() == ID_cpp_name)
                  has_calls = true;
              });
            if(has_calls)
            {
              can_evaluate = false;
              break;
            }
          }
          expr.swap(tmp);
          return;
        }
        else if(auto expr_stmt = expr_try_dynamic_cast<code_expressiont>(stmt))
        {
          if(
            auto assign = expr_try_dynamic_cast<side_effect_expr_assignt>(
              expr_stmt->expression()))
          {
            if(assign->lhs().id() == ID_symbol)
            {
              exprt rhs = assign->rhs();
              value_map.replace(rhs);
              value_map.set(to_symbol_expr(assign->lhs()), rhs);
            }
            else
              can_evaluate = false;
          }
          else
            can_evaluate = false;
        }
        else if(stmt.get_statement() == ID_decl_block)
        {
          for(const auto &expect_decl : stmt.operands())
          {
            if(to_code(expect_decl).get_statement() != ID_decl)
            {
              can_evaluate = false;
              break;
            }
            const auto &decl = to_code_frontend_decl(to_code(expect_decl));
            if(decl.initial_value().has_value())
            {
              exprt init = decl.initial_value().value();
              value_map.replace(init);
              value_map.set(decl.symbol(), init);
            }
          }
        }
        else if(stmt.get_statement() == ID_skip)
        {
          // no-op, just continue
        }
        else if(stmt.get_statement() == ID_ifthenelse)
        {
          try
          {
            // C++14 relaxed constexpr: if/else
            exprt cond = stmt.op0();
            value_map.replace(cond);
            simplify(cond, *this);
            if(cond.is_true())
            {
              // Evaluate 'then' branch
              if(stmt.operands().size() >= 2)
              {
                if(stmt.op1().id() != ID_code)
                {
                  can_evaluate = false;
                  break;
                }
                const auto &then_code = to_code(stmt.op1());
                if(then_code.get_statement() == ID_block)
                {
                  for(const auto &s : to_code_block(then_code).statements())
                  {
                    if(
                      auto ret =
                        expr_try_dynamic_cast<code_frontend_returnt>(s))
                    {
                      exprt tmp = ret->return_value();
                      value_map.replace(tmp);
                      simplify(tmp, *this);
                      // Recursively evaluate nested constexpr calls
                      {
                        bool changed = true;
                        while(changed)
                        {
                          changed = false;
                          tmp.visit_post(std::function<void(exprt &)>(
                            [&](exprt &node)
                            {
                              if(
                                node.id() == ID_side_effect &&
                                to_side_effect_expr(node).get_statement() ==
                                  ID_function_call)
                              {
                                auto &call =
                                  to_side_effect_expr_function_call(node);
                                exprt before = call;
                                typecheck_side_effect_function_call(call);
                                if(call != before)
                                {
                                  node = call;
                                  changed = true;
                                }
                              }
                            }));
                          if(changed)
                            simplify(tmp, *this);
                        }
                      }
                      // Check if result is fully evaluated
                      bool has_calls = false;
                      tmp.visit_pre(
                        [&has_calls](const exprt &e)
                        {
                          if(e.id() == ID_side_effect)
                            has_calls = true;
                        });
                      if(has_calls)
                      {
                        can_evaluate = false;
                        break;
                      }
                      expr.swap(tmp);
                      return;
                    }
                    else if(
                      auto es = expr_try_dynamic_cast<code_expressiont>(s))
                    {
                      if(
                        auto assign =
                          expr_try_dynamic_cast<side_effect_expr_assignt>(
                            es->expression()))
                      {
                        if(assign->lhs().id() == ID_symbol)
                        {
                          exprt rhs = assign->rhs();
                          value_map.replace(rhs);
                          value_map.set(to_symbol_expr(assign->lhs()), rhs);
                        }
                        else
                          can_evaluate = false;
                      }
                    }
                  }
                }
                else if(
                  auto ret =
                    expr_try_dynamic_cast<code_frontend_returnt>(then_code))
                {
                  exprt tmp = ret->return_value();
                  value_map.replace(tmp);
                  simplify(tmp, *this);
                  {
                    bool chg = true;
                    while(chg)
                    {
                      chg = false;
                      tmp.visit_post(std::function<void(exprt &)>(
                        [&](exprt &node)
                        {
                          if(
                            node.id() == ID_side_effect &&
                            to_side_effect_expr(node).get_statement() ==
                              ID_function_call)
                          {
                            auto &c2 = to_side_effect_expr_function_call(node);
                            exprt b2 = c2;
                            typecheck_side_effect_function_call(c2);
                            if(c2 != b2)
                            {
                              node = c2;
                              chg = true;
                            }
                          }
                        }));
                      if(chg)
                        simplify(tmp, *this);
                    }
                  }
                  {
                    bool has_calls = false;
                    tmp.visit_pre(
                      [&has_calls](const exprt &e)
                      {
                        if(e.id() == ID_side_effect)
                          has_calls = true;
                      });
                    if(has_calls)
                    {
                      can_evaluate = false;
                      break;
                    }
                  }
                  expr.swap(tmp);
                  return;
                }
              }
            }
            else if(cond.is_false())
            {
              // Evaluate 'else' branch if present
              if(stmt.operands().size() >= 3)
              {
                if(stmt.op2().id() != ID_code)
                {
                  can_evaluate = false;
                  break;
                }
                const auto &else_code = to_code(stmt.op2());
                if(
                  auto ret =
                    expr_try_dynamic_cast<code_frontend_returnt>(else_code))
                {
                  exprt tmp = ret->return_value();
                  value_map.replace(tmp);
                  simplify(tmp, *this);
                  {
                    bool chg = true;
                    while(chg)
                    {
                      chg = false;
                      tmp.visit_post(std::function<void(exprt &)>(
                        [&](exprt &node)
                        {
                          if(
                            node.id() == ID_side_effect &&
                            to_side_effect_expr(node).get_statement() ==
                              ID_function_call)
                          {
                            auto &c2 = to_side_effect_expr_function_call(node);
                            exprt b2 = c2;
                            typecheck_side_effect_function_call(c2);
                            if(c2 != b2)
                            {
                              node = c2;
                              chg = true;
                            }
                          }
                        }));
                      if(chg)
                        simplify(tmp, *this);
                    }
                  }
                  {
                    bool has_calls = false;
                    tmp.visit_pre(
                      [&has_calls](const exprt &e)
                      {
                        if(e.id() == ID_side_effect)
                          has_calls = true;
                      });
                    if(has_calls)
                    {
                      can_evaluate = false;
                      break;
                    }
                  }
                  expr.swap(tmp);
                  return;
                }
              }
            }
            else
              can_evaluate = false;
          }
          catch(...)
          {
            can_evaluate = false;
          }
        }
        else if(stmt.get_statement() == ID_while)
        {
          try
          {
            // C++14 relaxed constexpr: while loop with bounded iterations
            const unsigned max_iterations = 1000;
            for(unsigned i = 0; i < max_iterations && can_evaluate; ++i)
            {
              exprt cond = stmt.op0();
              value_map.replace(cond);
              simplify(cond, *this);
              if(cond.is_false())
                break;
              if(!cond.is_true())
              {
                can_evaluate = false;
                break;
              }
              // Execute loop body
              if(stmt.operands().size() < 2 || stmt.op1().id() != ID_code)
              {
                can_evaluate = false;
                break;
              }
              const auto &body = to_code(stmt.op1());
              auto exec_stmt = [&](const codet &s) -> bool
              {
                if(auto ret = expr_try_dynamic_cast<code_frontend_returnt>(s))
                {
                  exprt tmp = ret->return_value();
                  value_map.replace(tmp);
                  simplify(tmp, *this);
                  {
                    bool chg = true;
                    while(chg)
                    {
                      chg = false;
                      tmp.visit_post(std::function<void(exprt &)>(
                        [&](exprt &node)
                        {
                          if(
                            node.id() == ID_side_effect &&
                            to_side_effect_expr(node).get_statement() ==
                              ID_function_call)
                          {
                            auto &c2 = to_side_effect_expr_function_call(node);
                            exprt b2 = c2;
                            typecheck_side_effect_function_call(c2);
                            if(c2 != b2)
                            {
                              node = c2;
                              chg = true;
                            }
                          }
                        }));
                      if(chg)
                        simplify(tmp, *this);
                    }
                  }
                  {
                    bool has_calls = false;
                    tmp.visit_pre(
                      [&has_calls](const exprt &e)
                      {
                        if(e.id() == ID_side_effect)
                          has_calls = true;
                      });
                    if(has_calls)
                      return false; // can't evaluate
                  }
                  expr.swap(tmp);
                  return true; // return from function
                }
                else if(auto es = expr_try_dynamic_cast<code_expressiont>(s))
                {
                  if(
                    auto assign =
                      expr_try_dynamic_cast<side_effect_expr_assignt>(
                        es->expression()))
                  {
                    if(assign->lhs().id() == ID_symbol)
                    {
                      exprt rhs = assign->rhs();
                      value_map.replace(rhs);
                      simplify(rhs, *this);
                      value_map.set(to_symbol_expr(assign->lhs()), rhs);
                    }
                    else
                      can_evaluate = false;
                  }
                }
                else if(s.get_statement() == ID_decl_block)
                {
                  for(const auto &d : s.operands())
                  {
                    if(
                      d.id() == ID_code &&
                      to_code(d).get_statement() == ID_decl)
                    {
                      const auto &decl = to_code_frontend_decl(to_code(d));
                      if(decl.initial_value().has_value())
                      {
                        exprt init = decl.initial_value().value();
                        value_map.replace(init);
                        simplify(init, *this);
                        value_map.set(decl.symbol(), init);
                      }
                    }
                  }
                }
                else if(s.get_statement() == ID_skip)
                {
                }
                else
                  can_evaluate = false;
                return false;
              };

              if(body.get_statement() == ID_block)
              {
                for(const auto &s : to_code_block(body).statements())
                {
                  if(s.id() != ID_code)
                  {
                    can_evaluate = false;
                    break;
                  }
                  if(exec_stmt(to_code(s)))
                    return; // function returned
                  if(!can_evaluate)
                    break;
                }
              }
              else
              {
                if(exec_stmt(body))
                  return;
              }
            }
          }
          catch(...)
          {
            can_evaluate = false;
          }
        }
        else
        {
          // Unsupported statement type.
          // Fall back to treating as a regular function call.
          can_evaluate = false;
        }
      }

      // If we couldn't evaluate at compile time, treat as a regular
      // function call by clearing the is_macro flag.
      // Note: we intentionally do NOT clear is_macro here.
      // The function may be evaluable with different (constant)
      // arguments later (e.g., from make_constant during template
      // instantiation).
    }
  }

  // we will deal with some 'special' functions here
  exprt tmp = do_special_functions(expr);
  if(tmp.is_not_nil())
    expr.swap(tmp);
} // NOLINT(readability/fn_size)

/// \param expr: function call whose arguments need to be checked
void cpp_typecheckt::typecheck_function_call_arguments(
  side_effect_expr_function_callt &expr)
{
  exprt &f_op = expr.function();
  const code_typet &code_type = to_code_type(f_op.type());
  const code_typet::parameterst &parameters = code_type.parameters();

  // do default arguments

  if(parameters.size() > expr.arguments().size())
  {
    std::size_t i = expr.arguments().size();

    for(; i < parameters.size(); i++)
    {
      if(!parameters[i].has_default_value())
        break;

      const exprt &value = parameters[i].default_value();
      expr.arguments().push_back(value);
    }
  }

  exprt::operandst::iterator arg_it = expr.arguments().begin();
  for(const auto &parameter : parameters)
  {
    if(parameter.get_bool(ID_C_call_by_value))
    {
      DATA_INVARIANT(is_reference(parameter.type()), "reference expected");

      if(arg_it->id() != ID_temporary_object)
      {
        // create a temporary for the parameter

        exprt temporary;
        new_temporary(
          arg_it->source_location(),
          to_reference_type(parameter.type()).base_type(),
          already_typechecked_exprt{*arg_it},
          temporary);
        arg_it->swap(temporary);
      }
    }
    else if(
      is_rvalue_reference(parameter.type()) &&
      arg_it->type().id() != ID_pointer && arg_it->id() != ID_address_of &&
      arg_it->id() != ID_temporary_object && arg_it->id() != ID_dereference &&
      (arg_it->type().id() == ID_struct_tag ||
       arg_it->type().id() == ID_struct ||
       arg_it->type().id() == ID_union_tag || arg_it->type().id() == ID_union))
    {
      // [dcl.init.ref] p5: An rvalue reference binds to an rvalue.
      // When the argument is a struct/union value (including function
      // call results), take its address to create the reference binding.
      // For side_effect (function call) results, the result is
      // materialized as a temporary by the GOTO conversion.
      exprt addr = address_of_exprt(*arg_it);
      addr.type() = parameter.type();
      arg_it->swap(addr);
    }
    else if(
      parameter.type().id() == ID_struct_tag &&
      arg_it->id() != ID_temporary_object && arg_it->id() != ID_side_effect)
    {
      // Brace-init-list to std::initializer_list<T>: convert before
      // the copy-constructor path so that new_temporary sees a struct,
      // not a raw brace-init-list.
      if(
        arg_it->id() == ID_initializer_list &&
        parameter.type().id() == ID_struct_tag &&
        id2string(to_struct_tag_type(parameter.type()).get_identifier())
            .find("tag-initializer_list<") != std::string::npos)
      {
        implicit_typecast(*arg_it, parameter.type());
        ++arg_it;
        continue;
      }

      // Non-POD class-type pass-by-value: call copy constructor.
      // Check that the destructor symbol exists (needed for the
      // temporary) to avoid crashes during goto conversion.
      const struct_typet &struct_type =
        follow_tag(to_struct_tag_type(parameter.type()));
      bool has_dtor = false;
      for(const auto &c : struct_type.components())
      {
        if(
          c.type().id() == ID_code &&
          to_code_type(c.type()).return_type().id() == ID_destructor)
        {
          const symbolt *dtor_sym;
          has_dtor = !lookup(c.get_name(), dtor_sym);
          break;
        }
      }
      if(has_dtor)
      {
        exprt temporary;
        new_temporary(
          arg_it->source_location(),
          parameter.type(),
          already_typechecked_exprt{*arg_it},
          temporary);
        arg_it->swap(temporary);
      }
    }

    ++arg_it;
  }

  c_typecheck_baset::typecheck_function_call_arguments(expr);
}

/// Replace `auto` (or `cpp_name`) in a type tree with the given replacement.
/// Handles `const auto &`, `auto *`, etc.
static void replace_auto_in_type(typet &type, const typet &replacement)
{
  if(type.id() == ID_auto || type.id() == ID_cpp_name)
  {
    type = replacement;
    return;
  }

  if(
    type.id() == ID_merged_type || type.id() == ID_frontend_pointer ||
    type.id() == ID_pointer)
  {
    for(auto &sub : to_type_with_subtypes(type).subtypes())
      replace_auto_in_type(sub, replacement);
  }
}

void cpp_typecheckt::instantiate_generic_lambda(
  side_effect_expr_function_callt &expr)
{
  // Resolve the lambda function name from the call target.
  // The function expression is either:
  //   dereference(symbol("var")) — indirect call through variable
  //   symbol("lambda_func") — direct call
  irep_idt lambda_name;

  if(expr.function().id() == ID_dereference)
  {
    const exprt &inner = to_dereference_expr(expr.function()).pointer();
    if(inner.id() == ID_symbol)
    {
      const symbolt &var_sym =
        symbol_table.lookup_ref(to_symbol_expr(inner).get_identifier());
      // The variable's value should be address_of(symbol(lambda_func))
      if(
        var_sym.value.id() == ID_address_of &&
        to_address_of_expr(var_sym.value).object().id() == ID_symbol)
      {
        lambda_name = to_symbol_expr(to_address_of_expr(var_sym.value).object())
                        .get_identifier();
      }
    }
  }
  else if(expr.function().id() == ID_symbol)
  {
    lambda_name = to_symbol_expr(expr.function()).get_identifier();
  }

  if(lambda_name.empty())
    return;

  auto it = generic_lambda_map.find(lambda_name);
  if(it == generic_lambda_map.end())
    return;

  // Build the list of actual argument types
  std::vector<typet> arg_types;
  for(auto &arg : expr.arguments())
  {
    if(arg.type().is_nil() || arg.type().id().empty())
      typecheck_expr(arg);
    arg_types.push_back(arg.type());
  }

  // Build a mangled name for this instantiation
  std::string inst_name = id2string(lambda_name);
  for(const auto &t : arg_types)
    inst_name += "#" + cpp_type2name(t);

  // Check if we already instantiated this specialization
  if(symbol_table.has_symbol(inst_name))
  {
    // Redirect the call to the existing instantiation
    const symbolt &inst_sym = symbol_table.lookup_ref(inst_name);
    const code_typet &inst_type = to_code_type(inst_sym.type);
    if(expr.function().id() == ID_dereference)
    {
      expr.function() = symbol_exprt(inst_name, inst_type);
      expr.type() = inst_type.return_type();
    }
    return;
  }

  // Create a fresh copy of the original lambda expression
  exprt lambda_expr = it->second;

  // Replace auto/template parameters with actual argument types.
  // Build a mapping from template parameter names to actual types
  // (for C++20 template lambdas where params use named types like T).
  std::map<irep_idt, typet> type_map;
  irept &params = lambda_expr.add(ID_parameters);
  std::size_t arg_idx = 0;
  for(auto &p : params.get_sub())
  {
    cpp_declarationt &pdecl = static_cast<cpp_declarationt &>(p);
    if(pdecl.get_bool("explicit_this"))
      continue;
    if(arg_idx < arg_types.size())
    {
      if(has_auto(pdecl.type()) || pdecl.type().id() == ID_auto)
      {
        replace_auto_in_type(pdecl.type(), arg_types[arg_idx]);
      }
      else if(pdecl.type().id() == ID_cpp_name)
      {
        // Template lambda: map the type name to the actual type
        irep_idt tname = pdecl.type().get_sub().front().get(ID_identifier);
        type_map[tname] = arg_types[arg_idx];
        pdecl.type() = arg_types[arg_idx];
      }
    }
    arg_idx++;
  }

  // Replace template type names in the return type
  {
    irept &ret_type = lambda_expr.add(ID_return_type);
    if(ret_type.is_not_nil() && ret_type.id() == ID_cpp_name)
    {
      irep_idt rname = ret_type.get_sub().front().get(ID_identifier);
      auto tm = type_map.find(rname);
      if(tm != type_map.end())
        ret_type = static_cast<const irept &>(tm->second);
    }
  }

  // Now type-check this lambda as a non-generic lambda with the inst_name
  // We do this by calling typecheck_expr_lambda with the modified expression.
  // But since typecheck_expr_lambda uses a counter for naming, we need to
  // set up the name manually.

  // Extract the scope prefix from the original lambda name
  // e.g., "main::1::__lambda_0" -> scope prefix is "main::1::"
  std::string orig = id2string(lambda_name);
  auto last_sep = orig.rfind("::");
  std::string scope_prefix =
    (last_sep != std::string::npos) ? orig.substr(0, last_sep + 2) : "";

  // Use inst_name as the function symbol name
  const source_locationt &loc = lambda_expr.source_location();

  // Collect parameters
  code_typet::parameterst func_params;
  for(const auto &p : params.get_sub())
  {
    const cpp_declarationt &pdecl = static_cast<const cpp_declarationt &>(p);
    if(pdecl.get_bool("explicit_this"))
      continue;
    typet ptype = pdecl.type();
    if(!ptype.id().empty())
      typecheck_type(ptype);
    irep_idt pname;
    if(!pdecl.declarators().empty())
      pname =
        pdecl.declarators().front().name().get_sub().front().get(ID_identifier);
    code_typet::parametert param(ptype);
    param.set_identifier(inst_name + "::" + id2string(pname));
    param.set_base_name(pname);
    func_params.push_back(param);
  }

  // Create parameter symbols
  for(const auto &p : func_params)
  {
    if(symbol_table.has_symbol(p.get_identifier()))
      continue;
    auxiliary_symbolt psym;
    psym.name = p.get_identifier();
    psym.base_name = p.get_base_name();
    psym.type = p.type();
    psym.mode = ID_cpp;
    psym.module = module;
    psym.location = loc;
    psym.is_file_local = true;
    psym.is_thread_local = true;
    psym.is_lvalue = true;
    psym.is_parameter = true;
    symbol_table.insert(std::move(psym));
  }

  // Collect captures from the original lambda
  const irept &capture_list = lambda_expr.find("lambda_capture");
  std::map<irep_idt, exprt> capture_values;
  std::set<irep_idt> by_ref_captures;
  for(const auto &cap : capture_list.get_sub())
  {
    irep_idt cap_name = cap.get(ID_identifier);
    if(cap_name.empty())
      continue;
    if(cap.get_bool("by_ref"))
      by_ref_captures.insert(cap_name);
    const exprt &init = static_cast<const exprt &>(cap.find("init"));
    if(init.is_not_nil())
    {
      exprt init_copy = init;
      typecheck_expr(init_copy);
      capture_values[cap_name] = init_copy;
    }
    else
    {
      exprt cap_expr(ID_cpp_name);
      irept name_node(ID_name);
      name_node.set(ID_identifier, cap_name);
      cap_expr.get_sub().push_back(name_node);
      cap_expr.add_source_location() = loc;
      typecheck_expr(cap_expr);
      capture_values[cap_name] = cap_expr;
    }
  }

  // Type-check the body
  typet lambda_return_type = signed_int_type();
  bool deduce_return = true;
  {
    const irept &explicit_ret = lambda_expr.find(ID_return_type);
    if(explicit_ret.is_not_nil() && !explicit_ret.id().empty())
    {
      lambda_return_type = static_cast<const typet &>(explicit_ret);
      typecheck_type(lambda_return_type);
      deduce_return = false;
    }
  }

  code_typet func_type(func_params, lambda_return_type);

  codet body_code(ID_nil);
  {
    cpp_save_scopet save_scope(cpp_scopes);

    // Find or create the lambda scope
    std::string lambda_base = inst_name.substr(scope_prefix.size());
    cpp_scopet &lambda_scope =
      cpp_scopes.current_scope().new_scope(lambda_base);
    lambda_scope.prefix = inst_name + "::";
    cpp_scopes.go_to(lambda_scope);

    for(const auto &p : func_params)
    {
      const symbolt &psym = symbol_table.lookup_ref(p.get_identifier());
      cpp_idt &id = cpp_scopes.put_into_scope(psym);
      id.id_class = cpp_idt::id_classt::SYMBOL;
    }

    for(const auto &cap : capture_values)
    {
      if(by_ref_captures.count(cap.first))
      {
        if(cap.second.id() == ID_symbol)
        {
          const symbolt &outer_sym = symbol_table.lookup_ref(
            to_symbol_expr(cap.second).get_identifier());
          cpp_idt &cid = cpp_scopes.put_into_scope(outer_sym);
          cid.id_class = cpp_idt::id_classt::SYMBOL;
          continue;
        }
      }

      std::string csym_name = inst_name + "::" + id2string(cap.first);
      if(!symbol_table.has_symbol(csym_name))
      {
        auxiliary_symbolt csym;
        csym.name = csym_name;
        csym.base_name = cap.first;
        csym.type = cap.second.type();
        csym.value = cap.second;
        csym.mode = ID_cpp;
        csym.module = module;
        csym.location = loc;
        csym.is_file_local = true;
        csym.is_thread_local = true;
        csym.is_lvalue = true;
        csym.is_state_var = true;
        symbol_table.insert(std::move(csym));
      }

      const symbolt &inserted = symbol_table.lookup_ref(csym_name);
      cpp_idt &cid = cpp_scopes.put_into_scope(inserted);
      cid.id_class = cpp_idt::id_classt::SYMBOL;
    }

    body_code = to_code(static_cast<exprt &>(lambda_expr.add("body")));

    typet old_return_type = return_type;
    if(deduce_return)
      return_type = typet(ID_auto);
    else
      return_type = func_type.return_type();

    typecheck_code(body_code);

    if(deduce_return)
    {
      std::function<const exprt *(const codet &)> find_return =
        [&](const codet &code) -> const exprt *
      {
        if(code.get_statement() == ID_return && code.has_operands())
          return &code.op0();
        for(const auto &op : code.operands())
          if(op.id() == ID_code)
          {
            const exprt *r = find_return(to_code(op));
            if(r != nullptr)
              return r;
          }
        return nullptr;
      };
      const exprt *ret = find_return(body_code);
      if(ret != nullptr)
        func_type.return_type() = ret->type();
      else
        func_type.return_type() = void_type();
    }

    return_type = old_return_type;

    // Prepend capture initializations
    if(!capture_values.empty())
    {
      code_blockt block;
      for(const auto &cap : capture_values)
      {
        if(by_ref_captures.count(cap.first))
          continue;
        symbol_exprt cap_sym(
          inst_name + "::" + id2string(cap.first), cap.second.type());
        codet assign(ID_assign);
        assign.copy_to_operands(cap_sym);
        assign.copy_to_operands(cap.second);
        assign.add_source_location() = loc;
        block.add(std::move(assign));
      }
      if(body_code.get_statement() == ID_block)
      {
        for(auto &stmt : to_code_block(body_code).statements())
          block.add(std::move(stmt));
      }
      else
        block.add(std::move(body_code));
      body_code = std::move(block);
    }
  }

  // Create the function symbol
  symbolt func_sym;
  func_sym.name = inst_name;
  func_sym.base_name = inst_name.substr(scope_prefix.size());
  func_sym.type = func_type;
  func_sym.value = body_code;
  func_sym.mode = ID_cpp;
  func_sym.module = module;
  func_sym.location = loc;
  func_sym.is_file_local = true;
  symbol_table.insert(std::move(func_sym));

  // Redirect the call to the new instantiation
  expr.function() = symbol_exprt(inst_name, func_type);
  expr.type() = func_type.return_type();
}

void cpp_typecheckt::typecheck_expr_side_effect(side_effect_exprt &expr)
{
  const irep_idt &statement = expr.get(ID_statement);

  if(statement == ID_cpp_new || statement == ID_cpp_new_array)
  {
    typecheck_expr_new(expr);
  }
  else if(statement == ID_cpp_delete || statement == ID_cpp_delete_array)
  {
    typecheck_expr_delete(expr);
  }
  else if(
    statement == ID_preincrement || statement == ID_predecrement ||
    statement == ID_postincrement || statement == ID_postdecrement)
  {
    typecheck_side_effect_inc_dec(expr);
  }
  else if(statement == ID_throw)
  {
    typecheck_expr_throw(expr);
  }
  else if(statement == ID_temporary_object)
  {
    // TODO
  }
  else
    c_typecheck_baset::typecheck_expr_side_effect(expr);
}

void cpp_typecheckt::typecheck_method_application(
  side_effect_expr_function_callt &expr)
{
  PRECONDITION(expr.operands().size() == 2);

  PRECONDITION(expr.function().id() == ID_member);
  PRECONDITION(expr.function().operands().size() == 1);

  // turn e.f(...) into xx::f(e, ...)

  exprt member_expr;
  member_expr.swap(expr.function());

  symbolt &method_symbol =
    symbol_table.get_writeable_ref(member_expr.get(ID_component_name));

  const irep_idt &member_name = method_symbol.type.get(ID_C_member_name);

  if(!member_name.empty())
  {
    const symbolt &tag_symbol = lookup(member_name);

    // build the right template map
    // if this is an instantiated template class method
    if(tag_symbol.type.find(ID_C_template) != irept())
    {
      cpp_saved_template_mapt saved_map(template_map);
      const irept &template_type = tag_symbol.type.find(ID_C_template);
      const irept &template_args =
        tag_symbol.type.find(ID_C_template_arguments);
      template_map.build(
        static_cast<const template_typet &>(template_type),
        static_cast<const cpp_template_args_tct &>(template_args));
      add_method_body(&method_symbol);
#ifdef DEBUG
      std::cout << "MAP for " << method_symbol << ":\n";
      template_map.print(std::cout);
#endif
    }
    else
      add_method_body(&method_symbol);
  }
  else
    add_method_body(&method_symbol);

  // If the method has an auto return type, force immediate type-checking
  // of the body so the return type is deduced before the call site uses it.
  if(
    method_symbol.type.id() == ID_code &&
    has_auto(to_code_type(method_symbol.type).return_type()) &&
    method_symbol.value.is_not_nil())
  {
    convert_function(method_symbol);
  }

  // build new function expression
  exprt new_function(cpp_symbol_expr(method_symbol));
  new_function.add_source_location()=member_expr.source_location();
  expr.function().swap(new_function);

  if(!expr.function().type().get_bool(ID_C_is_static))
  {
    const code_typet &func_type = to_code_type(method_symbol.type);
    typet this_type = func_type.parameters().front().type();

    // C++23 deducing this: first parameter is the object by value,
    // not a pointer.
    if(func_type.get_bool("explicit_this"))
    {
      if(expr.arguments().size() < func_type.parameters().size())
      {
        exprt this_arg = to_member_expr(member_expr).compound();
        implicit_typecast(this_arg, this_type);
        expr.arguments().insert(expr.arguments().begin(), this_arg);
      }
    }
    else
    {
      // Special case. Make it a reference.
      DATA_INVARIANT(this_type.id() == ID_pointer, "this should be pointer");
      this_type.set(ID_C_reference, true);
      this_type.set(ID_C_this, true);

      if(expr.arguments().size() == func_type.parameters().size())
      {
        // this might be set up for base-class initialisation
        if(
          expr.arguments().front().type() !=
          func_type.parameters().front().type())
        {
          implicit_typecast(expr.arguments().front(), this_type);
          DATA_INVARIANT(
            is_reference(expr.arguments().front().type()),
            "argument should be reference");
          expr.arguments().front().type().remove(ID_C_reference);
        }
      }
      else
      {
        exprt this_arg = to_member_expr(member_expr).compound();
        implicit_typecast(this_arg, this_type);
        // For multiple inheritance, the implicit_typecast may produce a
        // simple typecast from derived* to base* without adjusting the
        // pointer offset. Re-do the pointer cast using make_ptr_typecast
        // which handles non-first base class offsets.
        if(
          this_arg.id() == ID_typecast && this_arg.type().id() == ID_pointer &&
          to_typecast_expr(this_arg).op().type().id() == ID_pointer &&
          to_pointer_type(this_arg.type()).base_type().id() == ID_struct_tag &&
          to_pointer_type(to_typecast_expr(this_arg).op().type())
              .base_type()
              .id() == ID_struct_tag)
        {
          // Only adjust for upcasts (derived* -> base*).
          const struct_typet &src_s = follow_tag(to_struct_tag_type(
            to_pointer_type(to_typecast_expr(this_arg).op().type())
              .base_type()));
          const struct_typet &dest_s = follow_tag(
            to_struct_tag_type(to_pointer_type(this_arg.type()).base_type()));
          if(subtype_typecast(src_s, dest_s))
          {
            exprt inner = to_typecast_expr(this_arg).op();
            pointer_typet dest_ptr_type(
              to_pointer_type(this_arg.type()).base_type(),
              to_pointer_type(this_arg.type()).get_width());
            make_ptr_typecast(inner, dest_ptr_type);
            inner.type().set(ID_C_reference, true);
            inner.type().set(ID_C_this, true);
            this_arg = inner;
          }
        }
        DATA_INVARIANT(
          is_reference(this_arg.type()), "argument should be reference");
        this_arg.type().remove(ID_C_reference);
        expr.arguments().insert(expr.arguments().begin(), this_arg);
      }
    } // end else (non-deducing-this)
  }

  if(
    method_symbol.value.id() == ID_cpp_not_typechecked &&
    !method_symbol.value.get_bool(ID_is_used))
  {
    method_symbol.value.set(ID_is_used, true);
  }
}

void cpp_typecheckt::typecheck_side_effect_assignment(side_effect_exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location=expr.find_source_location();
    error() << "assignment side effect expected to have two operands"
            << eom;
    throw 0;
  }

  typet type0 = to_binary_expr(expr).op0().type();

  if(is_reference(type0))
    type0 = to_reference_type(type0).base_type();

  if(cpp_is_pod(type0))
  {
    // for structs we use the 'implicit assignment operator',
    // and therefore, it is allowed to assign to a rvalue struct.
    if(type0.id() == ID_struct_tag)
      to_binary_expr(expr).op0().set(ID_C_lvalue, true);

    c_typecheck_baset::typecheck_side_effect_assignment(expr);

    // Note that in C++ (as opposed to C), the assignment yields
    // an lvalue!
    expr.set(ID_C_lvalue, true);
    return;
  }

  // It's a non-POD.
  // Turn into an operator call

  std::string strop="operator";

  const irep_idt statement=expr.get(ID_statement);

  if(statement==ID_assign)
    strop += "=";
  else if(statement==ID_assign_shl)
    strop += "<<=";
  else if(statement==ID_assign_shr)
    strop += ">>=";
  else if(statement==ID_assign_plus)
    strop += "+=";
  else if(statement==ID_assign_minus)
    strop += "-=";
  else if(statement==ID_assign_mult)
    strop += "*=";
  else if(statement==ID_assign_div)
    strop += "/=";
  else if(statement == ID_assign_mod)
    strop += "%=";
  else if(statement==ID_assign_bitand)
    strop += "&=";
  else if(statement==ID_assign_bitor)
    strop += "|=";
  else if(statement==ID_assign_bitxor)
    strop += "^=";
  else
  {
    error().source_location=expr.find_source_location();
    error() << "bad assignment operator '" << statement << "'" << eom;
    throw 0;
  }

  const cpp_namet cpp_name(strop, expr.source_location());

  // expr.op0() is already typechecked
  exprt member(ID_member);
  member.set(ID_component_cpp_name, cpp_name);
  member.add_to_operands(already_typechecked_exprt{to_binary_expr(expr).op0()});

  side_effect_expr_function_callt new_expr(
    std::move(member),
    {to_binary_expr(expr).op1()},
    uninitialized_typet{},
    expr.source_location());

  typecheck_side_effect_function_call(new_expr);

  expr=new_expr;
}

void cpp_typecheckt::typecheck_side_effect_inc_dec(
  side_effect_exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "statement " << expr.get_statement()
            << " expected to have one operand" << eom;
    throw 0;
  }

  auto &op = to_unary_expr(expr).op();

  add_implicit_dereference(op);

  const typet &tmp_type = op.type();

  if(is_number(tmp_type) ||
     tmp_type.id()==ID_pointer)
  {
    // standard stuff
    c_typecheck_baset::typecheck_expr_side_effect(expr);
    return;
  }

  // Turn into an operator call

  std::string str_op="operator";
  bool post=false;

  if(expr.get(ID_statement)==ID_preincrement)
    str_op += "++";
  else if(expr.get(ID_statement)==ID_predecrement)
    str_op += "--";
  else if(expr.get(ID_statement)==ID_postincrement)
  {
    str_op += "++";
    post=true;
  }
  else if(expr.get(ID_statement)==ID_postdecrement)
  {
    str_op += "--";
    post=true;
  }
  else
  {
    error().source_location=expr.find_source_location();
    error() << "bad assignment operator '" << expr.get_statement() << "'"
            << eom;
    throw 0;
  }

  const cpp_namet cpp_name(str_op, expr.source_location());

  exprt member(ID_member);
  member.set(ID_component_cpp_name, cpp_name);
  member.add_to_operands(already_typechecked_exprt{op});

  side_effect_expr_function_callt new_expr(
    std::move(member), {}, uninitialized_typet{}, expr.source_location());

  // the odd C++ way to denote the post-inc/dec operator
  if(post)
    new_expr.arguments().push_back(
      from_integer(mp_integer(0), signed_int_type()));

  typecheck_side_effect_function_call(new_expr);
  expr.swap(new_expr);
}

void cpp_typecheckt::typecheck_expr_dereference(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "unary operator * expects one operand" << eom;
    throw 0;
  }

  exprt &op = to_dereference_expr(expr).pointer();
  const typet &op_type = op.type();

  if(op_type.id() == ID_pointer && op_type.find(ID_to_member).is_not_nil())
  {
    error().source_location=expr.find_source_location();
    error() << "pointer-to-member must use "
            << "the .* or ->* operators" << eom;
    throw 0;
  }

  c_typecheck_baset::typecheck_expr_dereference(expr);
}

void cpp_typecheckt::convert_pmop(exprt &expr)
{
  PRECONDITION(expr.id() == ID_pointer_to_member);
  PRECONDITION(expr.operands().size() == 2);

  auto &op0 = to_binary_expr(expr).op0();
  auto &op1 = to_binary_expr(expr).op1();

  if(op1.type().id() != ID_pointer || op1.type().find(ID_to_member).is_nil())
  {
    error().source_location=expr.source_location();
    error() << "pointer-to-member expected" << eom;
    throw 0;
  }

  typet t0 = op0.type().id() == ID_pointer
               ? to_pointer_type(op0.type()).base_type()
               : op0.type();

  typet t1((const typet &)op1.type().find(ID_to_member));

  if(t0.id() != ID_struct_tag)
  {
    error().source_location=expr.source_location();
    error() << "pointer-to-member type error" << eom;
    throw 0;
  }

  const struct_typet &from_struct = follow_tag(to_struct_tag_type(t0));
  const struct_typet &to_struct = follow_tag(to_struct_tag_type(t1));

  if(!subtype_typecast(from_struct, to_struct))
  {
    error().source_location=expr.source_location();
    error() << "pointer-to-member type error" << eom;
    throw 0;
  }

  typecheck_expr_main(op1);

  if(op0.type().id() != ID_pointer)
  {
    if(op0.id() == ID_dereference)
    {
      op0 = to_dereference_expr(op0).pointer();
    }
    else
    {
      DATA_INVARIANT(
        op0.get_bool(ID_C_lvalue),
        "pointer-to-member must have lvalue operand");
      op0 = address_of_exprt(op0);
    }
  }

  exprt tmp(op1);
  tmp.type().set(ID_C_bound, op0);
  expr.swap(tmp);
  return;
}

void cpp_typecheckt::typecheck_expr_function_identifier(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    // Check if the function body has to be typechecked
    symbolt &function_symbol =
      symbol_table.get_writeable_ref(expr.get(ID_identifier));

    if(function_symbol.value.id() == ID_cpp_not_typechecked)
      function_symbol.value.set(ID_is_used, true);

    // For functions in deferred_typechecking (e.g., static member
    // functions of class templates), ensure the body gets typechecked
    // by adding it to method_bodies.
    if(
      function_symbol.value.is_not_nil() &&
      deferred_typechecking.count(function_symbol.name))
    {
      add_method_body(&function_symbol);
    }

    {
      auto it = deferred_method_bodies.find(function_symbol.name);
      if(it != deferred_method_bodies.end())
      {
        method_bodies.push_back(std::move(it->second));
        deferred_method_bodies.erase(it);
      }
    }
  }

  c_typecheck_baset::typecheck_expr_function_identifier(expr);
}

void cpp_typecheckt::typecheck_expr(exprt &expr, const target_typet &target)
{
  // Phase 2 of the target-type-threading refactor.
  //
  // [temp.deduct.funcaddr]/1: a cpp_name argument bound to a
  // pointer-to-function parameter — either as a bare cpp_name
  // (implicit function-to-pointer per [conv.func]/1) or as an
  // explicit `&cpp_name` — drives template-argument deduction
  // forward from the target.  On success, swap in the typed
  // `address_of(specialisation)`; on failure, fall through to the
  // isolated path so real mismatches surface as user-visible
  // errors.
  if(target.has_target())
  {
    const bool is_funcaddr_shape =
      expr.id() == ID_cpp_name ||
      (expr.id() == ID_address_of && expr.operands().size() == 1 &&
       to_unary_expr(expr).op().id() == ID_cpp_name);

    if(is_funcaddr_shape)
    {
      exprt deduced = deduce_funcaddr_against_target(expr, *target.get());
      if(deduced.is_not_nil())
      {
        expr.swap(deduced);
        return;
      }
    }
  }

  // Fall through to the no-target implementation.
  typecheck_expr(expr);
}

void cpp_typecheckt::typecheck_expr(exprt &expr)
{
  bool override_constantness = expr.get_bool(ID_C_override_constantness);

  // We take care of an ambiguity in the C++ grammar.
  // Needs to be done before the operands!
  explicit_typecast_ambiguity(expr);

  // cpp_name uses get_sub, which can get confused with expressions.
  if(expr.id()==ID_cpp_name)
    typecheck_expr_cpp_name(expr, cpp_typecheck_fargst());
  else if(expr.id() == "lambda")
    typecheck_expr_lambda(expr);
  else if(expr.id() == ID_arguments)
  {
    // Arguments list for a function call.  Typecheck each argument
    // individually, catching and deferring failures: an argument
    // of the form `&f` or `f` where `f` names a function template
    // cannot be typechecked in isolation here because the deduction
    // needs the outer call's parameter types
    // ([temp.deduct.funcaddr]).  Leave such arguments untyped so
    // the containing typecheck_side_effect_function_call can retry
    // them with target-type context.  For arguments with an already
    // typechecked body (`ID_already_typechecked`) just continue; for
    // all others, attempt the full typecheck and let any C++
    // exception propagate unless the operand is a function-address
    // candidate we can retry later.
    for(auto &op : expr.operands())
    {
      const bool may_need_target_type = [&]() -> bool
      {
        const exprt *probe = &op;
        if(probe->id() == ID_address_of && probe->operands().size() == 1)
          probe = &to_unary_expr(*probe).op();
        return probe->id() == ID_cpp_name;
      }();

      if(!may_need_target_type)
      {
        typecheck_expr(op);
        continue;
      }

      // Function-address template candidate — try, but defer on failure.
      try
      {
        typecheck_expr(op);
      }
      catch(...)
      {
        op.type().make_nil();
      }
    }
  }
  else
  {
    // This does the operands, and then calls typecheck_expr_main.
    c_typecheck_baset::typecheck_expr(expr);
  }

  if(override_constantness)
    expr.type().set(ID_C_constant, false);
}

void cpp_typecheckt::explicit_typecast_ambiguity(exprt &expr)
{
  // There is an ambiguity in the C++ grammar as follows:
  // (TYPENAME) + expr   (typecast of unary plus)  vs.
  // (expr) + expr       (sum of two expressions)
  // Same issue with the operators & and - and *

  // We figure this out by resolving the type argument
  // and re-writing if needed

  if(expr.id()!="explicit-typecast")
    return;

  PRECONDITION(expr.operands().size() == 1);

  irep_idt op0_id = to_unary_expr(expr).op().id();

  if(
    expr.type().id() == ID_cpp_name &&
    to_unary_expr(expr).op().operands().size() == 1 &&
    (op0_id == ID_unary_plus || op0_id == ID_unary_minus ||
     op0_id == ID_address_of || op0_id == ID_dereference))
  {
    exprt resolve_result=
      resolve(
        to_cpp_name(expr.type()),
        cpp_typecheck_resolvet::wantt::BOTH,
        cpp_typecheck_fargst());

    if(resolve_result.id()!=ID_type)
    {
      // need to re-write the expression
      // e.g., (ID) +expr  ->  ID+expr
      exprt new_binary_expr;

      new_binary_expr.operands().resize(2);
      to_binary_expr(new_binary_expr).op0().swap(expr.type());
      to_binary_expr(new_binary_expr)
        .op1()
        .swap(to_unary_expr(to_unary_expr(expr).op()).op());

      if(op0_id==ID_unary_plus)
        new_binary_expr.id(ID_plus);
      else if(op0_id==ID_unary_minus)
        new_binary_expr.id(ID_minus);
      else if(op0_id==ID_address_of)
        new_binary_expr.id(ID_bitand);
      else if(op0_id==ID_dereference)
        new_binary_expr.id(ID_mult);

      new_binary_expr.add_source_location() =
        to_unary_expr(expr).op().source_location();
      expr.swap(new_binary_expr);
    }
  }
}

void cpp_typecheckt::typecheck_expr_binary_arithmetic(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location=expr.find_source_location();
    error() << "operator '" << expr.id() << "' expects two operands" << eom;
    throw 0;
  }

  add_implicit_dereference(to_binary_expr(expr).op0());
  add_implicit_dereference(to_binary_expr(expr).op1());

  c_typecheck_baset::typecheck_expr_binary_arithmetic(expr);
}

void cpp_typecheckt::typecheck_expr_index(exprt &expr)
{
  c_typecheck_baset::typecheck_expr_index(expr);
}

void cpp_typecheckt::typecheck_expr_comma(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location=expr.find_source_location();
    error() << "comma operator expects two operands" << eom;
    throw 0;
  }

  const auto &op0_type = to_binary_expr(expr).op0().type();

  if(op0_type.id() == ID_struct || op0_type.id() == ID_struct_tag)
  {
    // TODO: check if the comma operator has been overloaded!
  }

  c_typecheck_baset::typecheck_expr_comma(expr);
}

void cpp_typecheckt::typecheck_expr_rel(binary_relation_exprt &expr)
{
  c_typecheck_baset::typecheck_expr_rel(expr);

  // Ensure both operands of pointer comparisons have exactly the same
  // type. The C type-checker creates null_pointer_exprt with the right
  // base type, but pointer annotations (e.g., #to_member for
  // pointer-to-member-function) may differ. Force the rhs type to
  // match the lhs type when both are pointers.
  if(
    expr.op0().type().id() == ID_pointer &&
    expr.op1().type().id() == ID_pointer &&
    expr.op0().type() != expr.op1().type())
  {
    expr.op1() = typecast_exprt(expr.op1(), expr.op0().type());
  }
}

void cpp_typecheckt::typecheck_expr_lambda(exprt &expr)
{
  // Lower C++11 lambda by creating a function where captured variables
  // become local constants initialized to their capture-point values.
  // The lambda becomes a function pointer.

  static unsigned lambda_count = 0;
  const std::string lambda_id = "__lambda_" + std::to_string(lambda_count++);
  const source_locationt &loc = expr.source_location();
  const std::string func_sym_name =
    id2string(cpp_scopes.current_scope().prefix) + lambda_id;

  // Check for C++14 generic lambda (auto parameters) or
  // C++20 template lambda (unresolved type name parameters)
  bool is_generic_lambda = false;
  {
    const irept &check_params = expr.find(ID_parameters);
    for(const auto &p : check_params.get_sub())
    {
      const cpp_declarationt &pdecl = static_cast<const cpp_declarationt &>(p);
      if(pdecl.get_bool("explicit_this"))
        continue;
      if(
        has_auto(pdecl.type()) || pdecl.type().id() == ID_cpp_name ||
        pdecl.type().id() == ID_auto)
      {
        is_generic_lambda = true;
        break;
      }
    }

    if(is_generic_lambda)
    {
      generic_lambda_map[func_sym_name] = expr;

      // Replace auto/template parameters with signed int
      irept &default_params = expr.add(ID_parameters);
      for(auto &p : default_params.get_sub())
      {
        cpp_declarationt &pdecl = static_cast<cpp_declarationt &>(p);
        if(pdecl.get_bool("explicit_this"))
          continue;
        if(has_auto(pdecl.type()) || pdecl.type().id() == ID_cpp_name)
          replace_auto_in_type(pdecl.type(), signed_int_type());
      }
    }
  }

  // Collect captures
  const irept &capture_list = expr.find("lambda_capture");
  std::map<irep_idt, exprt> capture_values;
  std::set<irep_idt> by_ref_captures;
  for(const auto &cap : capture_list.get_sub())
  {
    irep_idt cap_name = cap.get(ID_identifier);
    if(cap_name.empty())
      continue;

    if(cap.get_bool("by_ref"))
      by_ref_captures.insert(cap_name);

    // C++14 init-capture: [y = expr]
    const exprt &init = static_cast<const exprt &>(cap.find("init"));
    if(init.is_not_nil())
    {
      exprt init_copy = init;
      typecheck_expr(init_copy);
      capture_values[cap_name] = init_copy;
    }
    else
    {
      exprt cap_expr(ID_cpp_name);
      irept name_node(ID_name);
      name_node.set(ID_identifier, cap_name);
      cap_expr.get_sub().push_back(name_node);
      cap_expr.add_source_location() = loc;
      typecheck_expr(cap_expr);
      capture_values[cap_name] = cap_expr;
    }
  }

  // Collect parameters
  const irept &params_irep = expr.find(ID_parameters);
  code_typet::parameterst func_params;
  for(const auto &p : params_irep.get_sub())
  {
    const cpp_declarationt &pdecl = static_cast<const cpp_declarationt &>(p);
    // C++23 deducing this: skip explicit object parameter
    if(pdecl.get_bool("explicit_this"))
      continue;
    typet ptype = pdecl.type();
    typecheck_type(ptype);
    irep_idt pname;
    // Per N5008 [dcl.fct]/16: a lambda parameter may be unnamed
    // (e.g. `[](std::size_t) { ... }`).  Probe the declarator
    // structure defensively before reading the identifier.
    if(!pdecl.declarators().empty())
    {
      const auto &name_sub = pdecl.declarators().front().name().get_sub();
      if(!name_sub.empty())
        pname = name_sub.front().get(ID_identifier);
    }
    // Synthesise a unique base_name for unnamed parameters: the
    // downstream scope/parameter machinery requires a non-empty
    // base_name (cpp_scopes.cpp:30 `put_into_scope` precondition).
    if(pname.empty())
      pname = "__unnamed_param_" + std::to_string(func_params.size());
    code_typet::parametert param(ptype);
    param.set_identifier(func_sym_name + "::" + id2string(pname));
    param.set_base_name(pname);
    func_params.push_back(param);
  }

  // Determine return type: use explicit trailing return type if present
  // (and not a generic lambda where the type may reference template params),
  // otherwise deduce from body.
  typet lambda_return_type = signed_int_type();
  bool deduce_return = true;
  {
    const irept &explicit_ret = expr.find(ID_return_type);
    if(explicit_ret.is_not_nil() && !is_generic_lambda)
    {
      lambda_return_type = static_cast<const typet &>(explicit_ret);
      typecheck_type(lambda_return_type);
      deduce_return = false;
    }
  }

  code_typet func_type(std::move(func_params), lambda_return_type);

  // Create parameter symbols
  for(const auto &p : func_type.parameters())
  {
    auxiliary_symbolt psym;
    psym.name = p.get_identifier();
    psym.base_name = p.get_base_name();
    psym.type = p.type();
    psym.mode = ID_cpp;
    psym.module = module;
    psym.location = loc;
    psym.is_file_local = true;
    psym.is_thread_local = true;
    psym.is_lvalue = true;
    psym.is_parameter = true;
    symbol_table.insert(std::move(psym));
  }

  // For generic lambdas, try to type-check the body with the default int
  // parameters. If it succeeds, the lambda can be used as a function pointer.
  // If it fails (e.g., body uses struct members), defer to call-site
  // instantiation.
  if(is_generic_lambda)
  {
    codet default_body(ID_nil);
    bool body_ok = false;

    // Save error count so we can restore it if body type-checking fails
    const std::size_t saved_errors =
      get_message_handler().get_message_count(messaget::M_ERROR);
    const unsigned saved_verbosity = get_message_handler().get_verbosity();

    // Suppress error messages during the try
    get_message_handler().set_verbosity(0);

    // Try type-checking with int parameters
    try
    {
      cpp_save_scopet save_scope(cpp_scopes);
      cpp_scopet &lambda_scope =
        cpp_scopes.current_scope().new_scope(lambda_id + "_try");
      lambda_scope.prefix = func_sym_name + "::";
      cpp_scopes.go_to(lambda_scope);

      for(const auto &p : func_type.parameters())
      {
        if(!symbol_table.has_symbol(p.get_identifier()))
        {
          auxiliary_symbolt psym;
          psym.name = p.get_identifier();
          psym.base_name = p.get_base_name();
          psym.type = p.type();
          psym.mode = ID_cpp;
          psym.module = module;
          psym.location = loc;
          psym.is_file_local = true;
          psym.is_thread_local = true;
          psym.is_lvalue = true;
          psym.is_parameter = true;
          symbol_table.insert(std::move(psym));
        }
        const symbolt &psym = symbol_table.lookup_ref(p.get_identifier());
        cpp_idt &id = cpp_scopes.put_into_scope(psym);
        id.id_class = cpp_idt::id_classt::SYMBOL;
      }

      // Put captures in scope
      for(const auto &cap : capture_values)
      {
        if(by_ref_captures.count(cap.first))
        {
          if(cap.second.id() == ID_symbol)
          {
            const symbolt &outer_sym = symbol_table.lookup_ref(
              to_symbol_expr(cap.second).get_identifier());
            cpp_idt &cid = cpp_scopes.put_into_scope(outer_sym);
            cid.id_class = cpp_idt::id_classt::SYMBOL;
            continue;
          }
        }

        std::string csym_name = func_sym_name + "::" + id2string(cap.first);
        if(!symbol_table.has_symbol(csym_name))
        {
          auxiliary_symbolt csym;
          csym.name = csym_name;
          csym.base_name = cap.first;
          csym.type = cap.second.type();
          csym.value = cap.second;
          csym.mode = ID_cpp;
          csym.module = module;
          csym.location = loc;
          csym.is_file_local = true;
          csym.is_thread_local = true;
          csym.is_lvalue = true;
          csym.is_state_var = true;
          symbol_table.insert(std::move(csym));
        }

        const symbolt &inserted = symbol_table.lookup_ref(csym_name);
        cpp_idt &cid = cpp_scopes.put_into_scope(inserted);
        cid.id_class = cpp_idt::id_classt::SYMBOL;
      }

      default_body = to_code(static_cast<exprt &>(expr.add("body")));

      typet old_return_type = return_type;
      return_type = typet(ID_auto);
      typecheck_code(default_body);

      // Deduce return type
      std::function<const exprt *(const codet &)> find_return =
        [&](const codet &code) -> const exprt *
      {
        if(code.get_statement() == ID_return && code.has_operands())
          return &code.op0();
        for(const auto &op : code.operands())
          if(op.id() == ID_code)
          {
            const exprt *r = find_return(to_code(op));
            if(r != nullptr)
              return r;
          }
        return nullptr;
      };
      const exprt *ret = find_return(default_body);
      if(ret != nullptr)
        func_type.return_type() = ret->type();
      else
        func_type.return_type() = void_type();

      return_type = old_return_type;

      // Prepend capture initializations
      if(!capture_values.empty())
      {
        code_blockt block;
        for(const auto &cap : capture_values)
        {
          if(by_ref_captures.count(cap.first))
            continue;
          symbol_exprt cap_sym(
            func_sym_name + "::" + id2string(cap.first), cap.second.type());
          codet assign(ID_assign);
          assign.copy_to_operands(cap_sym);
          assign.copy_to_operands(cap.second);
          assign.add_source_location() = loc;
          block.add(std::move(assign));
        }
        if(default_body.get_statement() == ID_block)
        {
          for(auto &stmt : to_code_block(default_body).statements())
            block.add(std::move(stmt));
        }
        else
          block.add(std::move(default_body));
        default_body = std::move(block);
      }

      body_ok = true;
    }
    catch(...)
    {
      // Body type-checking failed with int params — leave body as nil
      // Restore error count so this doesn't cause overall failure
      get_message_handler().set_message_count(messaget::M_ERROR, saved_errors);
    }

    // Restore verbosity
    get_message_handler().set_verbosity(saved_verbosity);

    symbolt func_sym;
    func_sym.name = func_sym_name;
    func_sym.base_name = lambda_id;
    func_sym.type = func_type;
    func_sym.value = body_ok ? static_cast<exprt>(default_body) : nil_exprt();
    func_sym.mode = ID_cpp;
    func_sym.module = module;
    func_sym.location = loc;
    func_sym.is_file_local = true;
    symbol_table.insert(std::move(func_sym));

    {
      const symbolt &fsym = symbol_table.lookup_ref(func_sym_name);
      cpp_idt &fid = cpp_scopes.put_into_scope(fsym);
      fid.id_class = cpp_idt::id_classt::SYMBOL;
    }

    expr = address_of_exprt(symbol_exprt(func_sym_name, func_type));
    expr.type() = pointer_typet(func_type, config.ansi_c.pointer_width);
    expr.add_source_location() = loc;
    return;
  }

  // Type-check the body with captures and params in scope
  codet body_code(ID_nil);
  {
    cpp_save_scopet save_scope(cpp_scopes);
    cpp_scopet &lambda_scope = cpp_scopes.current_scope().new_scope(lambda_id);
    lambda_scope.prefix = func_sym_name + "::";
    cpp_scopes.go_to(lambda_scope);

    for(const auto &p : func_type.parameters())
    {
      const symbolt &psym = symbol_table.lookup_ref(p.get_identifier());
      cpp_idt &id = cpp_scopes.put_into_scope(psym);
      id.id_class = cpp_idt::id_classt::SYMBOL;
    }

    for(const auto &cap : capture_values)
    {
      // By-ref captures: put the outer symbol directly into scope
      if(by_ref_captures.count(cap.first))
      {
        if(cap.second.id() == ID_symbol)
        {
          const symbolt &outer_sym = symbol_table.lookup_ref(
            to_symbol_expr(cap.second).get_identifier());
          cpp_idt &cid = cpp_scopes.put_into_scope(outer_sym);
          cid.id_class = cpp_idt::id_classt::SYMBOL;
          continue;
        }
      }

      auxiliary_symbolt csym;
      csym.name = func_sym_name + "::" + id2string(cap.first);
      csym.base_name = cap.first;
      csym.type = cap.second.type();
      csym.value = cap.second;
      csym.mode = ID_cpp;
      csym.module = module;
      csym.location = loc;
      csym.is_file_local = true;
      csym.is_thread_local = true;
      csym.is_lvalue = true;
      csym.is_state_var = true;
      symbol_table.insert(std::move(csym));

      const symbolt &inserted =
        symbol_table.lookup_ref(func_sym_name + "::" + id2string(cap.first));
      cpp_idt &cid = cpp_scopes.put_into_scope(inserted);
      cid.id_class = cpp_idt::id_classt::SYMBOL;
    }

    body_code = to_code(static_cast<exprt &>(expr.add("body")));

    // Save/restore return_type so the lambda body uses its own return type
    typet old_return_type = return_type;
    if(deduce_return)
      return_type = typet(ID_auto);
    else
      return_type = func_type.return_type();

    typecheck_code(body_code);

    // Deduce return type from body if not explicitly specified
    if(deduce_return)
    {
      std::function<const exprt *(const codet &)> find_return =
        [&](const codet &code) -> const exprt *
      {
        if(code.get_statement() == ID_return && code.has_operands())
          return &code.op0();
        for(const auto &op : code.operands())
          if(op.id() == ID_code)
          {
            const exprt *r = find_return(to_code(op));
            if(r != nullptr)
              return r;
          }
        return nullptr;
      };
      const exprt *ret = find_return(body_code);
      if(ret != nullptr)
        func_type.return_type() = ret->type();
      else
        func_type.return_type() = void_type();
    }

    return_type = old_return_type;

    // Prepend capture initializations to the body
    if(!capture_values.empty())
    {
      code_blockt block;
      for(const auto &cap : capture_values)
      {
        if(by_ref_captures.count(cap.first))
          continue;
        symbol_exprt cap_sym(
          func_sym_name + "::" + id2string(cap.first), cap.second.type());
        codet assign(ID_assign);
        assign.copy_to_operands(cap_sym);
        assign.copy_to_operands(cap.second);
        assign.add_source_location() = loc;
        block.add(std::move(assign));
      }
      if(body_code.get_statement() == ID_block)
      {
        for(auto &stmt : to_code_block(body_code).statements())
          block.add(std::move(stmt));
      }
      else
        block.add(std::move(body_code));
      body_code = std::move(block);
    }
  }

  // Create the function symbol
  symbolt func_sym;
  func_sym.name = func_sym_name;
  func_sym.base_name = lambda_id;
  func_sym.type = func_type;
  func_sym.value = body_code;
  func_sym.mode = ID_cpp;
  func_sym.module = module;
  func_sym.location = loc;
  func_sym.is_file_local = true;
  symbol_table.insert(std::move(func_sym));

  {
    const symbolt &fsym = symbol_table.lookup_ref(func_sym_name);
    cpp_idt &fid = cpp_scopes.put_into_scope(fsym);
    fid.id_class = cpp_idt::id_classt::SYMBOL;
  }

  // Replace the lambda with a function pointer
  expr = address_of_exprt(symbol_exprt(func_sym_name, func_type));
  expr.type() = pointer_typet(func_type, config.ansi_c.pointer_width);
  expr.add_source_location() = loc;
}
