/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/mathematical_types.h>
#include <util/simplify_expr.h>
#include <util/source_location.h>
#include <util/symbol_table_base.h>

#include <ansi-c/c_qualifiers.h>
#include <ansi-c/merged_type.h>

#include "cpp_convert_type.h"
#include "cpp_declaration.h"
#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"

void cpp_typecheckt::typecheck_type(typet &type)
{
  // GCC 16+ headers may produce types with empty IDs from
  // constructs CBMC's parser doesn't fully handle (e.g.,
  // nested requires clauses). Skip rather than crash.
  if(type.id().empty() || type.is_nil())
    return;

  try
  {
    cpp_convert_plain_type(type, get_message_handler());
  }

  catch(const char *err)
  {
    error().source_location=type.source_location();
    error() << err << eom;
    throw 0;
  }

  catch(const std::string &err)
  {
    error().source_location=type.source_location();
    error() << err << eom;
    throw 0;
  }

  // N5008 [dcl.align]: fold the alignment-specifier to a constant, as
  // the C front end does (c_typecheck_type.cpp); otherwise an
  // alignas(type) member reaches struct layout as an unresolved
  // alignof expression and the alignment is silently treated as 1.
  // In a dependent context the fold can fail; leave the expression
  // as-is then -- the instantiation re-typechecks the member.
  if(type.find(ID_C_alignment).is_not_nil())
  {
    exprt &alignment = static_cast<exprt &>(type.add(ID_C_alignment));
    if(alignment.id() != ID_default && !alignment.is_constant())
    {
      const std::size_t errors_before =
        get_message_handler().get_message_count(messaget::M_ERROR);
      try
      {
        exprt tmp = alignment;
        typecheck_expr(tmp);
        make_constant(tmp);
        alignment = std::move(tmp);
      }
      catch(...)
      {
        get_message_handler().set_message_count(
          messaget::M_ERROR, errors_before);
      }
    }
  }

  if(type.id() == ID_template_parameter_symbol_type)
  {
    // Per [temp.arg]/2: if this template parameter is bound
    // in the enclosing template_map, resolve it to the bound type.
    // Per [temp.arg]/2: if this template parameter is bound
    // in the enclosing template_map, resolve it to the bound type.
    {
      typet resolved = type;
      template_map.apply(resolved);
      if(resolved.id() != ID_template_parameter_symbol_type)
      {
        type = resolved;
        return;
      }
    }
    const irep_idt &id =
      to_template_parameter_symbol_type(type).get_identifier();
    const symbolt *ttp_sym = symbol_table.lookup(id);
    if(ttp_sym && ttp_sym->type.get_bool(ID_is_template))
    {
      std::string bn = id2string(ttp_sym->base_name);
      if(bn.substr(0, 9) == "template.")
        bn = bn.substr(9);
      cpp_namet cpp_name{bn};
      type = static_cast<typet &>(static_cast<irept &>(cpp_name));
      // Fall through to cpp_name handler
    }
    else if(ttp_sym && ttp_sym->is_type)
    {
      type = ttp_sym->type;
      return;
    }
    else
      return;
  }

  if(type.id()==ID_cpp_name)
  {
    c_qualifierst qualifiers(type);

    cpp_namet cpp_name;
    cpp_name.swap(type);

    exprt symbol_expr;
    try
    {
      symbol_expr = resolve(
        cpp_name, cpp_typecheck_resolvet::wantt::TYPE, cpp_typecheck_fargst());
    }
    catch(...)
    {
      // The swap above moved the name OUT of `type`, so a resolution
      // failure would otherwise leave an EMPTY cpp_name behind.  When
      // `type` aliases a stored template declaration (e.g. a constraint
      // default argument `typename = _Require<...>` evaluated during
      // overload resolution, std::chrono::duration's converting
      // constructor), that gutted node PERSISTS: the template must remain
      // intact for later instantiations (a substitution failure is not an
      // error and has no lasting effect, N5008 [temp.deduct]/8), so every
      // later deduction would fail on the empty constraint.  Restore the
      // original name before propagating the failure.
      type.swap(cpp_name);
      throw;
    }

    if(symbol_expr.id()!=ID_type)
    {
      error().source_location=type.source_location();
      error() << "expected type" << eom;
      throw 0;
    }

    type=symbol_expr.type();
    PRECONDITION(type.is_not_nil());

    // Phase 2 audit per N5008 [temp.inst]/3.1: when a lazy typedef
    // symbol's alias type just propagated through here, drive
    // on-demand resolution.  The type itself carries the lazy
    // markers and class-scope identifier, so the type-only helper
    // can resolve it without needing back-pointers to the symbol.
    // The helper guards against re-entry into a class still being
    // typechecked.
    if(type.get_bool(ID_C_lazy_member_type))
      try_resolve_lazy_type(type);

    if(type.get_bool(ID_C_constant))
      qualifiers.is_constant = true;

    // CPROVER extensions
    irep_idt typedef_identifier = type.get(ID_C_typedef);
    if(typedef_identifier == CPROVER_PREFIX "rational")
    {
      type = rational_typet();
      type.add_source_location() = symbol_expr.source_location();
    }
    else if(typedef_identifier == CPROVER_PREFIX "integer")
    {
      type = integer_typet();
      type.add_source_location() = symbol_expr.source_location();
    }

    // N5008 [dcl.fct]/7: "The effect of a cv-qualifier-seq in a function
    // declarator is not the same as adding cv-qualification on top of the
    // function type.  In the latter case, the cv-qualifiers are ignored."
    // There are no cv-qualified function types.  When a cv-qualified template
    // parameter (`const T`) is substituted with a function type -- e.g.
    // `is_const<const _Tp>` with `_Tp` a function type, as used by libstdc++'s
    // `is_function<_Tp> = !is_const<const _Tp>` -- the const must be dropped
    // rather than written onto the function type; otherwise `is_const` is
    // wrongly true, `is_function` wrongly false, `decay` of a function type
    // misses function-to-pointer decay, and std::function's decayed `_Functor`
    // becomes a function type, breaking construction.
    if(type.id() == ID_code)
    {
      qualifiers.is_constant = false;
      qualifiers.is_volatile = false;
      type.remove(ID_C_constant);
      type.remove(ID_C_volatile);
    }

    qualifiers.write(type);
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    typecheck_compound_type(to_struct_union_type(type));
  }
  else if(type.id()==ID_pointer)
  {
    c_qualifierst qualifiers(type);

    // the pointer/reference might have a qualifier,
    // but do subtype first
    typecheck_type(to_pointer_type(type).base_type());

    // C++11 reference collapsing: if this is a reference/rvalue reference
    // and the base type is also a reference, collapse them.
    if(
      type.get_bool(ID_C_reference) &&
      to_pointer_type(type).base_type().id() == ID_pointer &&
      to_pointer_type(type).base_type().get_bool(ID_C_reference))
    {
      // The result is an lvalue reference unless both are rvalue references
      bool both_rvalue =
        type.get_bool(ID_C_rvalue_reference) &&
        to_pointer_type(type).base_type().get_bool(ID_C_rvalue_reference);
      type = to_pointer_type(type).base_type();
      if(!both_rvalue)
        type.remove(ID_C_rvalue_reference);
    }

    // Check if it is a pointer-to-member
    if(type.find(ID_to_member).is_not_nil())
    {
      // these can point either to data members or member functions
      // of a class

      typet &class_object = static_cast<typet &>(type.add(ID_to_member));

      if(class_object.id()==ID_cpp_name)
      {
        DATA_INVARIANT(
          class_object.get_sub().back().id() == "::", "scope suffix expected");
        class_object.get_sub().pop_back();
      }

      typecheck_type(class_object);

      // there may be parameters if this is a pointer to member function
      if(to_pointer_type(type).base_type().id() == ID_code)
      {
        code_typet::parameterst &parameters =
          to_code_type(to_pointer_type(type).base_type()).parameters();

        if(parameters.empty() || !parameters.front().get_this())
        {
          // Add 'this' to the parameters.  N5008 [dcl.fct]/6-7 +
          // [over.match.funcs]/4: the function type's cv-qualifier-seq
          // qualifies the implicit object parameter, so `int (S::*)(int)
          // const` and `int (S::*)(int)` are distinct types (the
          // libc++ __member_pointer_traits_imp partial specializations on
          // both) and `&S::f` for a const member matches the former.
          typet object_type = class_object;
          const irept &method_qualifier =
            to_pointer_type(type).base_type().find(ID_method_qualifier);
          if(method_qualifier.is_not_nil() && !method_qualifier.id().empty())
          {
            if(has_const(static_cast<const typet &>(method_qualifier)))
              object_type.set(ID_C_constant, true);
            if(has_volatile(static_cast<const typet &>(method_qualifier)))
              object_type.set(ID_C_volatile, true);
          }
          code_typet::parametert a0(pointer_type(object_type));
          a0.set_base_name(ID_this);
          a0.set_this();
          parameters.insert(parameters.begin(), a0);
        }
        to_pointer_type(type).base_type().remove(ID_method_qualifier);
      }
    }

    if(type.get_bool(ID_C_constant))
      qualifiers.is_constant = true;

    qualifiers.write(type);
  }
  else if(type.id()==ID_array)
  {
    exprt &size_expr=to_array_type(type).size();

    if(size_expr.is_not_nil())
    {
      // [dcl.array]: an array bound is a converted constant expression.
      constant_expression_contextt constant_expression_guard{*this};
      typecheck_expr(size_expr);
      simplify(size_expr, *this);
    }

    typecheck_type(to_array_type(type).element_type());

    if(to_array_type(type).element_type().get_bool(ID_C_constant))
      type.set(ID_C_constant, true);

    if(to_array_type(type).element_type().get_bool(ID_C_volatile))
      type.set(ID_C_volatile, true);
  }
  else if(type.id()==ID_vector)
  {
    // already done
  }
  else if(type.id() == ID_frontend_vector)
  {
    typecheck_vector_type(type);
  }
  else if(type.id()==ID_code)
  {
    code_typet &code_type=to_code_type(type);
    typecheck_type(code_type.return_type());

    code_typet::parameterst &parameters=code_type.parameters();

    for(auto &param : parameters)
    {
      typecheck_type(param.type());

      // A code type formed by template substitution from a parsed
      // function type may still carry a parameter as an unconverted
      // cpp_declaration (decl-specifier type + declarator).  When the
      // declarator applies a reference to a type that -- after
      // substitution -- is itself a reference (`_Mu_type<_BArgs,
      // _CallArgs>&&...` with an element `int&&`, libstdc++'s
      // _Bind::_Res_type), N5008 [dcl.ref]/7 collapses the two: an
      // rvalue reference to `TR` is `TR`, any other combination is an
      // lvalue reference to `T`.  Fold the collapsed reference into the
      // declaration's type and drop the declarator's, keeping the node's
      // shape; left as a reference-to-reference the parameter is
      // structurally unequal to the `_ArgTypes...` pattern element and
      // `result_of<_Functor(_ArgTypes...)>` never matches.
      if(param.id() == ID_cpp_declaration)
      {
        cpp_declarationt &declaration =
          static_cast<cpp_declarationt &>(static_cast<exprt &>(param));
        typet &decl_type = declaration.type();
        const bool type_is_ref = decl_type.id() == ID_pointer &&
                                 (decl_type.get_bool(ID_C_reference) ||
                                  decl_type.get_bool(ID_C_rvalue_reference));
        if(type_is_ref && !declaration.declarators().empty())
        {
          typet &declarator_type = declaration.declarators().front().type();
          const bool declarator_is_ref =
            (declarator_type.id() == ID_frontend_pointer ||
             declarator_type.id() == ID_pointer) &&
            (declarator_type.get_bool(ID_C_reference) ||
             declarator_type.get_bool(ID_C_rvalue_reference)) &&
            to_type_with_subtype(declarator_type).subtype().is_nil();
          if(declarator_is_ref)
          {
            const bool both_rvalue =
              declarator_type.get_bool(ID_C_rvalue_reference) &&
              decl_type.get_bool(ID_C_rvalue_reference);
            if(!both_rvalue)
              decl_type.remove(ID_C_rvalue_reference);
            declarator_type.make_nil();
          }
        }
      }

      // C/C++ function parameters of function or array type decay to
      // pointer type (C99 6.7.5.3, C++11 [dcl.fct] p5).
      adjust_function_parameter(param.type());

      // see if there is a default value
      if(param.has_default_value())
      {
        typecheck_expr(param.default_value());
        implicit_typecast(param.default_value(), param.type());
      }
    }
  }
  else if(type.id()==ID_template)
  {
    typecheck_type(to_template_type(type).subtype());
  }
  else if(type.id()==ID_c_enum)
  {
    typecheck_enum_type(type);
  }
  else if(type.id()==ID_c_enum_tag)
  {
  }
  else if(type.id()==ID_c_bit_field)
  {
    typecheck_c_bit_field_type(to_c_bit_field_type(type));
  }
  else if(
    type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
    type.id() == ID_bool || type.id() == ID_c_bool || type.id() == ID_floatbv ||
    type.id() == ID_fixedbv || type.id() == ID_empty)
  {
  }
  else if(type.id() == ID_struct_tag)
  {
  }
  else if(type.id() == ID_union_tag)
  {
  }
  else if(type.id()==ID_constructor ||
          type.id()==ID_destructor)
  {
  }
  else if(type.id()=="cpp-cast-operator")
  {
  }
  else if(type.id()=="cpp-template-type")
  {
  }
  else if(type.id()==ID_typeof)
  {
    exprt e=static_cast<const exprt &>(type.find(ID_expr_arg));

    if(e.is_nil())
    {
      typet tmp_type=
        static_cast<const typet &>(type.find(ID_type_arg));

      if(tmp_type.id()==ID_cpp_name)
      {
        // this may be ambiguous -- it can be either a type or
        // an expression

        cpp_typecheck_fargst fargs;

        exprt symbol_expr=resolve(
          to_cpp_name(static_cast<const irept &>(tmp_type)),
          cpp_typecheck_resolvet::wantt::BOTH,
          fargs);

        type=symbol_expr.type();
      }
      else
      {
        typecheck_type(tmp_type);
        type=tmp_type;
      }
    }
    else
    {
      typecheck_expr(e);
      type=e.type();
    }
  }
  else if(type.id()==ID_decltype)
  {
    // C++14: decltype(auto) — deduced from initializer, handled
    // during declarator conversion (like auto).
    if(type.get_bool("#auto"))
      return;

    exprt e=static_cast<const exprt &>(type.find(ID_expr_arg));

    // N5008 [expr.prim.fold] in a trailing-return-type decltype
    // ([dcl.fct]/8): fold-expressions are normally reduced in the
    // method-body pass, which does not run on a trailing return type;
    // the unexpanded `cpp_binary_fold`/`cpp_{left,right}_fold` then
    // fails to typecheck ("found no match for symbol '<fn>'"),
    // dropping the whole declaration.  When exactly one parameter
    // pack is bound in the current instantiation (pack_size_map), the
    // fold's element count is that size; reduce the fold to the
    // associated operator tree over the pattern here.  For a
    // single-element pack the sole element keeps the plain parameter
    // name (N5008 [temp.variadic]/5), so the pattern is used verbatim;
    // for an empty pack the identity value is used
    // ([expr.prim.fold]/3).  N>=2 (which requires replicated `$k`
    // parameters not yet present at this point) is left to the body
    // pass.
    if(template_map.pack_size_map.size() == 1)
    {
      const std::size_t pack_n = template_map.pack_size_map.begin()->second;
      const irep_idt fold_id_binary{"cpp_binary_fold"};
      const irep_idt fold_id_left{"cpp_left_fold"};
      const irep_idt fold_id_right{"cpp_right_fold"};
      std::function<void(irept &)> reduce = [&](irept &node)
      {
        const bool is_binary = node.id() == fold_id_binary;
        const bool is_left = node.id() == fold_id_left;
        const bool is_right = node.id() == fold_id_right;
        if(is_binary || is_left || is_right)
        {
          const irep_idt fold_op = node.get("fold_op");
          // Identify the pack-side of a binary fold by which operand
          // references a bound pack's parameter name (N5008
          // [expr.prim.fold]/2): `(pack op ... op init)` has the pack
          // on the LEFT (sub[0]); `(init op ... op pack)` on the
          // RIGHT (sub[1]).  A unary fold has the pattern as its sole
          // operand.
          std::function<bool(const irept &)> names_a_param =
            [&](const irept &n) -> bool
          {
            // a bare cpp_name / name that is NOT the pack's own type
            // parameter short-name but a value parameter -- for the
            // single/replicated value pack the pattern references the
            // PARAMETER, whose base name we detect structurally below;
            // here we only need "contains any cpp_name".
            if(n.id() == ID_cpp_name)
              return true;
            for(const auto &sn : n.get_sub())
              if(names_a_param(sn))
                return true;
            for(const auto &ns : n.get_named_sub())
              if(names_a_param(ns.second))
                return true;
            return false;
          };
          irept init_expr;
          irept pattern;
          bool binary_pack_on_left = false;
          if(is_binary && node.get_sub().size() >= 2)
          {
            const bool left_has = names_a_param(node.get_sub()[0]);
            const bool right_has = names_a_param(node.get_sub()[1]);
            // Prefer the side that references a name; if both do, the
            // init operand is the one WITHOUT the fold's pack -- fall
            // back to right-is-pattern (the common `(init op ... op
            // pack)`).
            if(left_has && !right_has)
            {
              pattern = node.get_sub()[0];
              init_expr = node.get_sub()[1];
              binary_pack_on_left = true;
            }
            else
            {
              init_expr = node.get_sub()[0];
              pattern = node.get_sub()[1];
            }
          }
          else if(!node.get_sub().empty())
            pattern = node.get_sub().front();
          else
            return;
          reduce(pattern);
          if(is_binary)
            reduce(init_expr);
          auto identity = [&]() -> irept
          {
            if(fold_op == ID_and)
              return true_exprt{};
            if(fold_op == ID_or)
              return false_exprt{};
            return from_integer(0, signed_int_type());
          };
          if(pack_n == 0)
          {
            node = is_binary ? init_expr : identity();
            return;
          }
          // pack_n == 1: the single element keeps the plain name.
          if(pack_n == 1)
          {
            if(is_binary)
            {
              irept bin(fold_op);
              if(binary_pack_on_left)
              {
                bin.get_sub().push_back(pattern);
                bin.get_sub().push_back(init_expr);
              }
              else
              {
                bin.get_sub().push_back(init_expr);
                bin.get_sub().push_back(pattern);
              }
              node = bin;
            }
            else
              node = pattern;
            return;
          }
          // pack_n >= 2: this trailing-return decltype is typechecked
          // during DEDUCTION, before the replicated `<base>$k` value
          // parameters exist -- their names cannot be used.  But
          // N5008 [dcl.type.decltype] only needs the TYPE of the
          // fold, and the pack's element TYPES are already deduced
          // (pack_args_map).  Expand the fold with typed PLACEHOLDER
          // operands: each pack-name reference in the pattern is
          // replaced by an already-typechecked nondet of the k-th
          // element type, so the operator tree typechecks to the
          // fold's result type and the placeholder values are
          // discarded with the decltype expression.  (Value-category
          // caveat: the placeholders are prvalues; a pattern whose
          // decltype hinges on the parameter's lvalueness would get T
          // rather than T& -- acceptable for the arithmetic fold
          // shapes of libc++'s __bind_back/ranges chain.)
          const auto pack_args_it = [&]()
          {
            for(auto it = template_map.pack_args_map.begin();
                it != template_map.pack_args_map.end();
                ++it)
            {
              if(it->second.size() == pack_n)
                return it;
            }
            return template_map.pack_args_map.end();
          }();
          if(pack_args_it == template_map.pack_args_map.end())
            return;
          const std::vector<typet> &elem_types = pack_args_it->second;
          irep_idt base;
          std::function<void(const irept &)> find_base = [&](const irept &n)
          {
            if(!base.empty())
              return;
            if(
              n.id() == ID_cpp_name && n.get_sub().size() == 1 &&
              n.get_sub().front().id() == ID_name)
              base = n.get_sub().front().get(ID_identifier);
            for(const auto &sn : n.get_sub())
              find_base(sn);
            for(const auto &ns : n.get_named_sub())
              find_base(ns.second);
          };
          find_base(pattern);
          if(base.empty())
            return;
          std::function<void(irept &, const typet &)> replace =
            [&](irept &n, const typet &t)
          {
            if(
              n.id() == ID_cpp_name && n.get_sub().size() == 1 &&
              n.get_sub().front().id() == ID_name &&
              n.get_sub().front().get(ID_identifier) == base)
            {
              typet elem_t = t;
              typecheck_type(elem_t);
              exprt placeholder =
                side_effect_expr_nondett{elem_t, source_locationt{}};
              already_typechecked_exprt::make_already_typechecked(placeholder);
              n = placeholder;
              return;
            }
            for(auto &sn : n.get_sub())
              replace(sn, t);
            for(auto &ns : n.get_named_sub())
              replace(ns.second, t);
          };
          auto elem = [&](std::size_t k) -> irept
          {
            irept c = pattern;
            replace(c, elem_types[k]);
            return c;
          };
          if(is_binary)
          {
            irept result = init_expr;
            if(binary_pack_on_left)
            {
              for(int k = static_cast<int>(pack_n) - 1; k >= 0; --k)
              {
                irept bin(fold_op);
                bin.get_sub().push_back(elem(static_cast<std::size_t>(k)));
                bin.get_sub().push_back(result);
                result = bin;
              }
            }
            else
            {
              for(std::size_t k = 0; k < pack_n; ++k)
              {
                irept bin(fold_op);
                bin.get_sub().push_back(result);
                bin.get_sub().push_back(elem(k));
                result = bin;
              }
            }
            node = result;
          }
          else if(is_left)
          {
            irept result = elem(0);
            for(std::size_t k = 1; k < pack_n; ++k)
            {
              irept bin(fold_op);
              bin.get_sub().push_back(result);
              bin.get_sub().push_back(elem(k));
              result = bin;
            }
            node = result;
          }
          else // right fold
          {
            irept result = elem(pack_n - 1);
            for(int k = static_cast<int>(pack_n) - 2; k >= 0; --k)
            {
              irept bin(fold_op);
              bin.get_sub().push_back(elem(static_cast<std::size_t>(k)));
              bin.get_sub().push_back(result);
              result = bin;
            }
            node = result;
          }
          return;
        }
        for(auto &s : node.get_sub())
          reduce(s);
        for(auto &ns : node.get_named_sub())
          reduce(ns.second);
      };
      reduce(e);
    }

    typecheck_expr(e);

    if(e.type().id() == ID_c_bit_field)
      type = to_c_bit_field_type(e.type()).underlying_type();
    else if(
      e.id() == ID_dereference && e.get_bool(ID_C_implicit) &&
      e.operands().size() == 1)
    {
      // The expression was implicitly dereferenced from a reference type.
      // decltype preserves the reference: decltype(f()) is T& if f returns T&.
      type = e.operands().front().type();
    }
    else if(
      e.id() == ID_dereference && e.type().id() != ID_code &&
      !e.type().get_bool(ID_C_reference))
    {
      // N5008 [dcl.type.decltype]/1.5: for any other expression E that is
      // an lvalue, decltype(E) is T&.  Indirection is an lvalue
      // ([expr.unary.op]/1), so decltype(*p) must be T&, not T (libc++'s
      // iter_reference_t is exactly `decltype(*declval<_Tp&>())`).
      type = ::reference_type(e.type());
    }
    else
      type = e.type();

    // If the expression is a lambda (address_of a function symbol),
    // store the lambda address so that default-initialization of
    // variables of this type can point to the lambda function.
    if(
      e.id() == ID_address_of &&
      to_address_of_expr(e).object().id() == ID_symbol)
    {
      type.set("#lambda_initializer", e);
    }
  }
  else if(type.id()==ID_unassigned)
  {
    // ignore, for template parameter guessing
  }
  else if(
    type.id() == ID_remove_cv || type.id() == ID_remove_reference ||
    type.id() == ID_remove_const || type.id() == ID_remove_volatile ||
    type.id() == ID_remove_cvref || type.id() == ID_remove_pointer ||
    type.id() == ID_remove_extent || type.id() == ID_remove_all_extents ||
    type.id() == ID_add_lvalue_reference ||
    type.id() == ID_add_rvalue_reference || type.id() == ID_add_pointer ||
    type.id() == ID_make_unsigned || type.id() == ID_make_signed)
  {
    typet tmp_type = static_cast<const typet &>(type.find(ID_type_arg));
    typecheck_type(tmp_type);

    if(type.id() == ID_remove_cv || type.id() == ID_remove_cvref)
    {
      tmp_type.remove(ID_C_constant);
      tmp_type.remove(ID_C_volatile);
    }

    // N5008 [meta.trans.cv]/2-3: remove_const removes only the
    // top-level const, remove_volatile only the top-level volatile
    // (clang's __remove_const/__remove_volatile builtins, used by
    // libc++'s __remove_const_t in <__atomic/cxx_atomic_impl.h>).
    if(type.id() == ID_remove_const)
      tmp_type.remove(ID_C_constant);
    if(type.id() == ID_remove_volatile)
      tmp_type.remove(ID_C_volatile);

    if(type.id() == ID_remove_reference || type.id() == ID_remove_cvref)
    {
      if(
        tmp_type.id() == ID_pointer &&
        (tmp_type.get_bool(ID_C_reference) ||
         tmp_type.get_bool(ID_C_rvalue_reference)))
      {
        tmp_type = to_pointer_type(tmp_type).base_type();
      }
    }

    if(type.id() == ID_remove_pointer)
    {
      if(
        tmp_type.id() == ID_pointer && !tmp_type.get_bool(ID_C_reference) &&
        !tmp_type.get_bool(ID_C_rvalue_reference))
      {
        tmp_type = to_pointer_type(tmp_type).base_type();
      }
    }

    if(type.id() == ID_remove_extent || type.id() == ID_remove_all_extents)
    {
      if(tmp_type.id() == ID_array)
      {
        tmp_type = to_array_type(tmp_type).element_type();
        // remove_all_extents: keep stripping array layers
        if(type.id() == ID_remove_all_extents)
        {
          while(tmp_type.id() == ID_array)
            tmp_type = to_array_type(tmp_type).element_type();
        }
      }
    }

    if(type.id() == ID_add_lvalue_reference)
    {
      // void stays void; otherwise add lvalue reference
      if(tmp_type.id() != ID_empty)
        tmp_type = ::reference_type(tmp_type);
    }

    if(type.id() == ID_add_rvalue_reference)
    {
      // void stays void; lvalue ref stays lvalue ref (ref collapsing)
      if(tmp_type.id() != ID_empty && !is_reference(tmp_type))
      {
        pointer_typet rref = pointer_type(tmp_type);
        // CBMC's convention marks an rvalue reference with BOTH
        // `#reference` and `#rvalue_reference` (see
        // cpp_convert_type.cpp); is_reference() tests only the former.
        // With only the rvalue flag the result read as a plain POINTER
        // downstream: a function template parameter declared
        // `__add_rvalue_reference(_Tp)` (gcc-16 <optional>'s
        // is_trivially_move_assignable_v helper) made every call
        // non-viable, since the scalar argument would not convert to
        // `_Tp *`.
        rref.set(ID_C_reference, true);
        rref.set(ID_C_rvalue_reference, true);
        tmp_type = std::move(rref);
      }
    }

    if(type.id() == ID_add_pointer)
    {
      // add_pointer<T&> = T*, add_pointer<T> = T*
      if(is_reference(tmp_type) || is_rvalue_reference(tmp_type))
        tmp_type = to_pointer_type(tmp_type).base_type();
      tmp_type = pointer_type(tmp_type);
    }

    if(type.id() == ID_make_unsigned || type.id() == ID_make_signed)
    {
      // Clang's __make_unsigned(T) / __make_signed(T) builtins, the
      // compiler-accelerated backing of N5008 [meta.trans.sign]:
      // the corresponding unsigned (signed) integer type of the same
      // width; cv-qualifiers are preserved ([meta.trans.sign]/2-3).
      // Enumerations convert to the signed/unsigned form of their
      // underlying type.
      const bool make_uns = type.id() == ID_make_unsigned;
      typet stripped = tmp_type;
      const bool was_const = stripped.get_bool(ID_C_constant);
      const bool was_volatile = stripped.get_bool(ID_C_volatile);
      stripped.remove(ID_C_constant);
      stripped.remove(ID_C_volatile);
      if(stripped.id() == ID_c_enum_tag)
        stripped = follow_tag(to_c_enum_tag_type(stripped)).underlying_type();
      typet result;
      if(stripped.id() == ID_unsignedbv || stripped.id() == ID_signedbv)
      {
        const std::size_t width = to_bitvector_type(stripped).get_width();
        if(make_uns)
          result = unsignedbv_typet{width};
        else
          result = signedbv_typet{width};
      }
      else if(stripped.id() == ID_c_bool || stripped.id() == ID_bool)
      {
        // not a valid argument per [meta.trans.sign]/1; keep as-is
        // (substitution failure surfaces at the use site)
        result = stripped;
      }
      else
        result = stripped;
      if(was_const)
        result.set(ID_C_constant, true);
      if(was_volatile)
        result.set(ID_C_volatile, true);
      tmp_type = result;
    }

    type = tmp_type;
  }
  else if(type.id()==ID_template_class_instance)
  {
    // ok (internally generated)
  }
  else if(type.id()==ID_block_pointer)
  {
    // This is an Apple extension for lambda-like constructs.
    // http://thirdcog.eu/pwcblocks/
    // we just treat them as references to functions
    type.id(ID_frontend_pointer);
    typecheck_type(type);
  }
  else if(type.id()==ID_nullptr)
  {
  }
  else if(type.id()==ID_already_typechecked)
  {
    c_typecheck_baset::typecheck_type(type);
  }
  else if(type.id() == ID_gcc_attribute_mode)
  {
    PRECONDITION(type.has_subtype());
    merged_typet as_parsed;
    as_parsed.move_to_subtypes(to_type_with_subtype(type).subtype());
    type.get_sub().clear();
    as_parsed.move_to_subtypes(type);
    type.swap(as_parsed);

    c_typecheck_baset::typecheck_type(type);
  }
  else if(type.id() == ID_complex)
  {
    // already done
  }
  else if(type.id() == ID_msc_underlying_type)
  {
    typet &type_arg = static_cast<typet &>(type.add(ID_type_arg));
    typecheck_type(type_arg);
    if(type_arg.id() == ID_c_enum_tag)
    {
      type = follow_tag(to_c_enum_tag_type(type_arg)).underlying_type();
    }
    else
    {
      // conservatively return int
      type = signed_int_type();
    }
  }
  else if(type.id() == ID_auto)
  {
    // C++11/14 auto type: leave as-is for deduction later.
    // For non-type template parameters, default to signed int.
  }
  else
  {
    error().source_location=type.source_location();
    error() << "unexpected cpp type: " << type.pretty() << eom;
    throw 0;
  }

  CHECK_RETURN(type.is_not_nil());
}
