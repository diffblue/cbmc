/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>

#include "cpp_typecheck.h"

/// \param source_location: source location for generated code
/// \param object: non-typechecked object
/// \param operands: non-typechecked operands
/// \return typechecked code
std::optional<codet> cpp_typecheckt::cpp_constructor(
  const source_locationt &source_location,
  const exprt &object,
  const exprt::operandst &operands)
{
  exprt object_tc = object;

  typecheck_expr(object_tc);

  elaborate_class_template(object_tc.type());

  CHECK_RETURN(!is_reference(object_tc.type()));

  if(object_tc.type().id() == ID_array)
  {
    // Deduce the bound of an array of unknown bound from its initializer
    // ([dcl.array]/1, [dcl.init.aggr]/5): the number of elements equals the
    // number of initializers.  This is needed for element types with a
    // non-trivial constructor, where initialization goes through per-element
    // construction below and would otherwise read a nil array size.  (Scalar
    // and trivial element types are sized on a separate initializer path.)
    if(to_array_type(object_tc.type()).size().is_nil() && !operands.empty())
    {
      const exprt &first_operand = operands.front();
      const std::size_t deduced_size = first_operand.get_bool(ID_C_array_ini)
                                         ? first_operand.operands().size()
                                         : operands.size();
      array_typet completed_type = to_array_type(object_tc.type());
      completed_type.size() = from_integer(deduced_size, c_index_type());
      object_tc.type() = completed_type;
    }

    // We allow only one operand and it must be tagged with '#array_ini'.
    // Note that the operand is an array that is used for copy-initialization.
    // In the general case, a program is not allowed to use this form of
    // construct. This way of initializing an array is used internally only.
    // The purpose of the tag #array_ini is to rule out ill-formed
    // programs.

    if(!operands.empty() && !operands.front().get_bool(ID_C_array_ini))
    {
      const array_typet &array_type = to_array_type(object_tc.type());
      const typet &element_type = array_type.element_type();

      // [dcl.init.aggr]/1, [dcl.init.list]/3: a class with a user-provided
      // constructor is not an aggregate, so each array element is
      // list-initialized by a constructor call rather than member-wise.  For
      // such element types, building an array_exprt from the brace elements (as
      // the aggregate/scalar path below does) would leave each element's
      // braced-init-list untyped -- indexing that array during construction
      // then yields a nil-typed expression that aborts simplification.  Detect a
      // user-provided constructor exactly as the base-class-aggregate code does
      // (a constructor component that is neither the default nor a copy/move
      // constructor, or a constructor template).
      bool element_has_user_ctor = false;
      if(element_type.id() == ID_struct_tag)
      {
        const struct_typet &element_struct =
          follow_tag(to_struct_tag_type(element_type));
        element_has_user_ctor =
          element_struct.get_bool("has_template_constructor");
        for(const auto &c : element_struct.components())
        {
          if(element_has_user_ctor)
            break;
          if(c.type().id() != ID_code || c.get_bool(ID_from_base))
            continue;
          const code_typet &ct = to_code_type(c.type());
          if(ct.return_type().id() != ID_constructor)
            continue;
          if(ct.parameters().size() <= 1) // default constructor
            continue;
          if(
            ct.parameters().size() == 2 &&
            is_reference(ct.parameters()[1].type())) // copy/move constructor
            continue;
          element_has_user_ctor = true;
        }
      }

      if(element_has_user_ctor)
      {
        // Construct each element in place from its own initializer-clause
        // ([dcl.init.aggr]/2): a brace-init element `{args}` forwards its
        // elements as the element's constructor arguments; a plain
        // value/temporary is a single initializer (copy/move construction); an
        // element without an initializer-clause is value-initialized.
        exprt tmp_size = array_type.size();
        make_constant_index(tmp_size);
        mp_integer array_size;
        if(to_integer(to_constant_expr(tmp_size), array_size))
        {
          error().source_location = source_location;
          error() << "array size '" << to_string(array_type.size())
                  << "' is not a constant" << eom;
          throw 0;
        }

        const std::size_t n = numeric_cast_v<std::size_t>(array_size);
        code_blockt new_code;
        for(std::size_t i = 0; i < n; ++i)
        {
          exprt constant = from_integer(i, c_index_type());
          constant.add_source_location() = source_location;
          index_exprt index{object_tc, constant};
          index.add_source_location() = source_location;

          exprt::operandst element_args;
          if(i < operands.size())
          {
            const exprt &init = operands[i];
            if(init.id() == ID_initializer_list)
              element_args = init.operands();
            else
              element_args.push_back(init);
          }

          auto element_code =
            cpp_constructor(source_location, index, element_args);
          if(element_code.has_value())
            new_code.add(std::move(element_code.value()));
        }
        return std::move(new_code);
      }

      // C++11 brace-enclosed initialization of an aggregate/scalar element
      // type: build an array expression from the individual operands and
      // assign it.
      array_exprt array_val(operands, array_type);
      array_val.add_source_location() = source_location;
      array_val.set(ID_C_array_ini, true);
      return cpp_constructor(source_location, object, {std::move(array_val)});
    }

    DATA_INVARIANT(
      operands.empty() || operands.size() == 1,
      "array constructor must have at most one operand");

    if(
      operands.empty() && cpp_is_pod(object_tc.type()) &&
      !has_default_member_initializer(object_tc.type()))
    {
      return {};
    }

    const exprt &size_expr = to_array_type(object_tc.type()).size();

    if(size_expr.id() == ID_infinity)
      return {}; // don't initialize

    exprt tmp_size = size_expr;
    make_constant_index(tmp_size);

    mp_integer s;
    if(to_integer(to_constant_expr(tmp_size), s))
    {
      error().source_location = source_location;
      error() << "array size '" << to_string(size_expr) << "' is not a constant"
              << eom;
      throw 0;
    }

    /*if(cpp_is_pod(object_tc.type()))
    {
      code_expressiont new_code;
      exprt op_tc=operands.front();
      typecheck_expr(op_tc);
       // Override constantness
      object_tc.type().set("ID_C_constant", false);
      object_tc.set("ID_C_lvalue", true);
      side_effect_exprt assign(ID_assign);
      assign.add_source_location()=source_location;
      assign.copy_to_operands(object_tc, op_tc);
      typecheck_side_effect_assignment(assign);
      new_code.expression()=assign;
      return new_code;
    }
    else*/
    {
      code_blockt new_code;

      // for each element of the array, call the default constructor
      for(mp_integer i = 0; i < s; ++i)
      {
        exprt::operandst tmp_operands;

        exprt constant = from_integer(i, c_index_type());
        constant.add_source_location() = source_location;

        index_exprt index = index_exprt(object_tc, constant);
        index.add_source_location() = source_location;

        if(!operands.empty())
        {
          index_exprt operand(operands.front(), constant);
          operand.add_source_location() = source_location;
          tmp_operands.push_back(operand);
        }

        auto i_code = cpp_constructor(source_location, index, tmp_operands);

        if(i_code.has_value())
          new_code.add(std::move(i_code.value()));
      }
      return std::move(new_code);
    }
  }
  else if(cpp_is_pod(object_tc.type()))
  {
    exprt::operandst operands_tc = operands;

    for(auto &op : operands_tc)
    {
      typecheck_expr(op);
      add_implicit_dereference(op);
    }

    if(operands_tc.empty())
    {
      // C++11: apply default member initializers for POD types
      if(object_tc.type().id() == ID_struct_tag)
      {
        const struct_typet &struct_type =
          follow_tag(to_struct_tag_type(object_tc.type()));
        code_blockt block;
        for(const auto &comp : struct_type.components())
        {
          if(
            comp.get_bool(ID_is_type) || comp.get_bool(ID_is_static) ||
            comp.type().id() == ID_code)
            continue;
          const irept &default_val = comp.find(ID_C_default_value);
          if(default_val.is_not_nil())
          {
            // Type-check in the class scope so that using-declarations
            // (e.g., using enum) are visible.
            cpp_save_scopet save_scope(cpp_scopes);
            cpp_scopes.set_scope(
              to_struct_tag_type(object_tc.type()).get_identifier());
            member_exprt member(object_tc, comp.get_name(), comp.type());
            member.set(ID_C_lvalue, true);

            // An empty brace initializer ({}) value-initializes the member
            // ([dcl.init]).  Type-checking the bare empty initializer_list
            // would otherwise yield a value with no determinate
            // representation (e.g. an initializer_list cast to a scalar,
            // which has no bit-width).  Use proper (zero-)value
            // initialization for any member type instead.
            if(
              default_val.id() == ID_initializer_list &&
              default_val.get_sub().empty())
            {
              auto zero =
                ::zero_initializer(comp.type(), source_location, *this);
              if(zero.has_value())
                block.add(
                  code_frontend_assignt(std::move(member), std::move(*zero)));
            }
            else
            {
              // N5008 [dcl.init.list], [dcl.init.aggr]: a non-empty braced
              // default member initializer initializes the member by
              // list-initialization -- a scalar from the single element
              // ([dcl.init.list]/3.9), an aggregate member-wise, a class via
              // its constructors.  Delegating to cpp_constructor (forwarding
              // the braced-init-list's elements as the initializer operands)
              // performs exactly that.  The previous code instead type-checked
              // the braced-init-list as a whole and cast it to the member type,
              // which left a raw initializer_list in the model (aborting the
              // bit-vector flattener for a scalar member, e.g. `int x{42}`).
              exprt init_val = static_cast<const exprt &>(default_val);
              exprt::operandst init_ops;
              if(init_val.id() == ID_initializer_list)
                init_ops = init_val.operands();
              else
                init_ops.push_back(std::move(init_val));

              auto member_init =
                cpp_constructor(source_location, member, init_ops);
              if(member_init.has_value())
                block.add(std::move(*member_init));
            }
          }
          else if(has_default_member_initializer(comp.type()))
          {
            // N5008 [class.base.init]/9-10: a member with no mem-initializer
            // and no default member initializer of its own, but whose type has
            // a non-trivial default constructor because a subobject carries a
            // default member initializer, is default-constructed.  Delegating
            // to cpp_constructor with no operands recursively applies the
            // subobject's initializers (e.g. `struct Q { int t = 5; }; struct
            // O { Q q; }; O o;` must leave `o.q.t == 5`).  A truly trivial
            // member is filtered out by has_default_member_initializer, so no
            // spurious construction code is added.
            cpp_save_scopet save_scope(cpp_scopes);
            cpp_scopes.set_scope(
              to_struct_tag_type(object_tc.type()).get_identifier());
            member_exprt member(object_tc, comp.get_name(), comp.type());
            member.set(ID_C_lvalue, true);
            exprt::operandst no_operands;
            auto member_init =
              cpp_constructor(source_location, member, no_operands);
            if(member_init.has_value())
              block.add(std::move(*member_init));
          }
        }
        if(!block.statements().empty())
          return std::move(block);
      }
      // a POD is NOT initialized
      return {};
    }
    else if(operands_tc.size() == 1)
    {
      exprt rhs = operands_tc.front();

      // N5008 [dcl.init.list]/3.9-3.11: when a scalar (more generally, a
      // non-class, non-array object) is list-initialized from a
      // braced-init-list with a single element, it is initialized from that
      // element.  A brace-init-list that reaches here as a raw
      // `initializer_list` operand -- e.g. a scalar member's braced default
      // member initializer `int x{42}` -- would otherwise be assigned to the
      // scalar wholesale and flow into GOTO conversion unresolved, aborting
      // the bit-vector flattener.  Unwrap it to its single element.  (An empty
      // `{}` has already been routed to value-initialization by the caller, so
      // only the single-element case needs handling here; a multi-element list
      // for a scalar is ill-formed and is left for the assignment below to
      // reject.)
      if(
        rhs.id() == ID_initializer_list && rhs.operands().size() == 1 &&
        object_tc.type().id() != ID_struct_tag &&
        object_tc.type().id() != ID_union_tag)
      {
        rhs = to_unary_expr(rhs).op();
      }

      // N5008 [dcl.init.list]/3.2 + /3.4: list-initializing a class from a
      // braced-init-list whose single element is of the SAME class type is
      // copy-initialization from that element; any other non-empty list for
      // an aggregate initializes it member-wise ([dcl.init.aggr]).  A POD
      // aggregate target (e.g. the base subobject in `Derived() : Base{42}`,
      // [class.base.init]/7) reached the assignment below with the raw list,
      // and the element-to-class implicit conversion was rejected
      // ("invalid implicit conversion from 'signed int' to 'struct Base'").
      if(
        rhs.id() == ID_initializer_list &&
        object_tc.type().id() == ID_struct_tag)
      {
        bool same_class_copy = false;
        if(rhs.operands().size() == 1)
        {
          exprt elem = to_unary_expr(rhs).op();
          typecheck_expr(elem);
          typet elem_type = elem.type();
          if(is_reference(elem_type))
            elem_type = to_reference_type(elem_type).base_type();
          same_class_copy =
            elem_type.id() == ID_struct_tag &&
            to_struct_tag_type(elem_type).get_identifier() ==
              to_struct_tag_type(object_tc.type()).get_identifier();
          if(same_class_copy)
            rhs = std::move(elem);
        }
        if(!same_class_copy)
        {
          // Member-wise aggregate initialization: hand the list's
          // elements to the parenthesized-aggregate branch below, which
          // implements exactly [dcl.init.aggr] (explicit elements in
          // order, trailing members value-initialized).
          exprt::operandst elements = rhs.operands();
          for(auto &e : elements)
          {
            typecheck_expr(e);
            add_implicit_dereference(e);
          }
          operands_tc = std::move(elements);
          goto aggregate_initialization;
        }
      }

      // Override constantness
      object_tc.type().set(ID_C_constant, false);
      object_tc.set(ID_C_lvalue, true);
      side_effect_expr_assignt assign(object_tc, rhs, typet(), source_location);
      typecheck_side_effect_assignment(assign);
      return code_expressiont(std::move(assign));
    }
    else
    {
    aggregate_initialization:
      // C++20 aggregate parenthesized initialization
      if(object_tc.type().id() == ID_struct_tag)
      {
        const struct_typet &struct_type =
          follow_tag(to_struct_tag_type(object_tc.type()));
        const auto &components = struct_type.components();
        code_blockt block;
        std::size_t idx = 0;
        for(const auto &comp : components)
        {
          if(
            comp.get_bool(ID_from_base) || comp.get_bool(ID_is_type) ||
            comp.get_bool(ID_is_static) || comp.type().id() == ID_code)
            continue;
          member_exprt member(object_tc, comp.get_name(), comp.type());
          member.set(ID_C_lvalue, true);
          exprt val;
          if(idx < operands_tc.size())
          {
            // look through an already_typechecked wrapper (nil-typed)
            const exprt &op_probe =
              operands_tc[idx].id() == ID_already_typechecked
                ? to_unary_expr(operands_tc[idx]).op()
                : operands_tc[idx];
            if(
              comp.type().id() == ID_array &&
              (op_probe.id() == ID_initializer_list ||
               op_probe.type().id() == ID_array ||
               to_array_type(comp.type()).size().is_constant()))
            {
              // N5008 [dcl.init.aggr]/4.2: an ARRAY element is itself
              // aggregate-initialized, element-wise -- arrays are not
              // assignable, so the assignment below would be rejected
              // ("direct assignments to arrays not permitted"; the
              // shape of a default member initializer `vec v_{{7,8}};`
              // whose member contains an array).  Recurse: a braced
              // list contributes its elements, an already-typed array
              // VALUE is copied element-wise by the array branch (it
              // requires the #array_ini tag).
              exprt array_member = member;
              already_typechecked_exprt::make_already_typechecked(
                array_member);
              exprt::operandst elem_ops;
              if(op_probe.id() == ID_initializer_list)
              {
                for(const auto &el : op_probe.operands())
                  elem_ops.push_back(already_typechecked_exprt{el});
              }
              else if(op_probe.type().id() == ID_array)
              {
                exprt aval = op_probe;
                aval.set(ID_C_array_ini, true);
                elem_ops.push_back(already_typechecked_exprt{aval});
              }
              else
              {
                // N5008 [dcl.init.aggr]/16 (brace elision): the
                // initializer list of the SUBAGGREGATE was elided; the
                // array element consumes the next N operands.
                const auto n = numeric_cast_v<std::size_t>(
                  to_constant_expr(to_array_type(comp.type()).size()));
                for(std::size_t k = 0; k < n && idx < operands_tc.size();
                    ++k, ++idx)
                {
                  elem_ops.push_back(
                    already_typechecked_exprt{operands_tc[idx]});
                }
                --idx; // the shared ++idx below advances past the last
              }
              auto elem_call =
                cpp_constructor(source_location, array_member, elem_ops);
              if(elem_call.has_value())
                block.add(std::move(*elem_call));
              ++idx;
              continue;
            }
            val =
              typecast_exprt::conditional_cast(operands_tc[idx], comp.type());
          }
          else
          {
            // N5008 [dcl.init.aggr]/5: elements without an explicit
            // initializer are initialized from their default member
            // initializer or copy-initialized from {} -- approximate
            // with zero initialization.  Trailing members were
            // previously left uninitialized (`aggt x(1, 2)` with three
            // members read garbage from the third).
            const auto zero = ::zero_initializer(
              comp.type(), source_location, namespacet{symbol_table});
            if(!zero.has_value())
            {
              ++idx;
              continue;
            }
            val = *zero;
          }
          side_effect_expr_assignt assign(
            std::move(member), std::move(val), typet(), source_location);
          typecheck_side_effect_assignment(assign);
          block.add(code_expressiont(std::move(assign)));
          ++idx;
        }
        return std::move(block);
      }
      error().source_location = source_location;
      error() << "initialization of POD requires one argument, "
                 "but got "
              << operands.size() << eom;
      throw 0;
    }
  }
  else if(object_tc.type().id() == ID_union_tag)
  {
    // [class.union]/2: a (non-POD) union may have a user-declared constructor;
    // construct it by an overload-resolved call to that constructor.  A union
    // has no base classes, virtual tables or most-derived flag, so this is the
    // constructor-call core of the struct case below.
    exprt::operandst operands_tc = operands;
    for(auto &op : operands_tc)
    {
      typecheck_expr(op);
      add_implicit_dereference(op);
    }

    const union_typet &union_type =
      follow_tag(to_union_tag_type(object_tc.type()));

    cpp_save_scopet save_scope(cpp_scopes);
    cpp_scopes.set_scope(union_type.get(ID_name));

    irep_idt constructor_name;
    for(const auto &c : union_type.components())
    {
      const typet &type = c.type();
      if(
        !c.get_bool(ID_from_base) && type.id() == ID_code &&
        to_code_type(type).return_type().id() == ID_constructor)
      {
        constructor_name = c.get_base_name();
        break;
      }
    }

    if(constructor_name.empty())
    {
      if(operands.empty())
        return code_expressiont{
          side_effect_expr_nondett{object.type(), source_location}};
      error().source_location = source_location;
      error() << "non-POD union has no constructor" << eom;
      throw 0;
    }

    side_effect_expr_function_callt function_call(
      cpp_namet(constructor_name, source_location).as_expr(),
      operands_tc,
      uninitialized_typet(),
      source_location);

    typecheck_side_effect_function_call(function_call);

    if(function_call.get(ID_statement) != ID_temporary_object)
    {
      error().source_location = source_location;
      error() << "constructor call did not resolve to temporary object" << eom;
      throw 0;
    }

    exprt &initializer =
      static_cast<exprt &>(function_call.add(ID_initializer));

    DATA_INVARIANT(
      initializer.id() == ID_code &&
        initializer.get(ID_statement) == ID_expression,
      "initializer must be expression statement");

    auto &statement_expr = to_code_expression(to_code(initializer));
    side_effect_expr_function_callt &func_ini =
      to_side_effect_expr_function_call(statement_expr.expression());
    exprt &tmp_this = func_ini.arguments().front();
    DATA_INVARIANT(
      to_address_of_expr(tmp_this).object().id() == ID_new_object,
      "expected new_object operand in address_of expression");
    tmp_this = address_of_exprt(object_tc);

    return to_code(initializer);
  }
  else if(object_tc.type().id() == ID_struct_tag)
  {
    exprt::operandst operands_tc = operands;

    for(auto &op : operands_tc)
    {
      typecheck_expr(op);
      add_implicit_dereference(op);
    }

    const struct_typet &struct_type =
      follow_tag(to_struct_tag_type(object_tc.type()));

    // C++17 aggregate initialization with base classes, and C++20
    // parenthesized aggregate initialization (P0960, N5008
    // [dcl.init.general]/16.6.2.2): if the struct has bases but no
    // user-declared constructors, initialize the elements from the
    // operands.  For a SINGLE operand this must not shadow copy/move
    // construction ([dcl.init.general]/16.6.1 considers constructors
    // first): skip when the operand is the class itself or derived
    // from it -- the synthesized copy/move constructor handles those.
    // N5008 [dcl.init.aggr]/1: an aggregate also must not have virtual
    // functions.  CBMC represents those via internal '@'-prefixed
    // components (vtable pointer); their presence disqualifies the
    // member-wise path (an operand must not be spliced into a vtable
    // slot).
    bool has_internal_component = false;
    for(const auto &c : struct_type.components())
    {
      if(
        !c.get_bool(ID_from_base) && c.type().id() != ID_code &&
        !c.get_bool(ID_is_type) && !c.get_bool(ID_is_static) &&
        has_prefix(id2string(c.get_base_name()), "@"))
      {
        has_internal_component = true;
        break;
      }
    }
    bool single_operand_aggregate = false;
    if(!has_internal_component && operands_tc.size() == 1)
    {
      typet op_t = operands_tc.front().type();
      if(op_t.id() == ID_struct_tag)
      {
        const irep_idt &op_id = to_struct_tag_type(op_t).get_identifier();
        single_operand_aggregate =
          op_id != to_struct_tag_type(object_tc.type()).get_identifier() &&
          !subtype_typecast(
            follow_tag(to_struct_tag_type(op_t)),
            follow_tag(to_struct_tag_type(object_tc.type())));
      }
      else
        single_operand_aggregate = true;
    }
    // C++20 parenthesized aggregate initialization applies regardless of
    // whether the aggregate has bases ([dcl.init.general]/16.6.2.2); the
    // no-bases case matters for aggregates that are non-POD only because
    // of a member, e.g. a REFERENCE member (`struct R { int &r; }; R
    // r(x);`), which otherwise fell through to constructor resolution
    // and failed against the synthesized copy constructor.
    if(
      !has_internal_component &&
      (operands_tc.size() >= 2 || single_operand_aggregate))
    {
      // [dcl.init.aggr]/1: a class with a user-declared constructor is not an
      // aggregate.  A template constructor is not stored as a regular component
      // (so the scan below would miss it); the struct carries a flag instead.
      // C++17: inherited constructors (using Base::Base) also make the class a
      // non-aggregate.
      bool has_user_ctor = struct_type.get_bool("has_template_constructor") ||
                           struct_type.get_bool("has_inherited_constructor");
      for(const auto &c : struct_type.components())
      {
        if(c.type().id() != ID_code || c.get_bool(ID_from_base))
          continue;
        const code_typet &ct = to_code_type(c.type());
        if(ct.return_type().id() != ID_constructor)
          continue;
        // N5008 [dcl.init.aggr]/1 (C++20 rule): ANY user-declared
        // constructor -- including a user-declared default or copy/move
        // constructor -- disqualifies the aggregate.  Only the
        // compiler-synthesized ones (marked #is_implicit_ctor) are
        // ignored.  The previous shape-based skip (this-only and
        // (this, reference) signatures) also skipped USER-declared
        // default constructors, so `base_type(10)` inside Constructor13
        // aggregate-initialized a class with user constructors.
        if(c.type().get_bool("#is_implicit_ctor"))
          continue;
        has_user_ctor = true;
        break;
      }
      if(!has_user_ctor)
      {
        code_blockt block;
        std::size_t idx = 0;
        // Initialize base class subobjects: for each base, the
        // corresponding operand initializes the from_base data members.
        for(std::size_t b = 0; b < struct_type.bases().size(); ++b)
        {
          if(idx >= operands_tc.size())
            break;
          // N5008 [dcl.init.aggr]/4.1: when the element is a BASE and
          // the initializer is of the base's own type (or derived),
          // the base SUBOBJECT is copy-initialized from it -- a sliced
          // whole-object copy, not a member-wise splice (member-wise
          // treated the whole takeish value as the first member's
          // initializer, leaving the base nondet: the closure CTAD
          // wrong-code shape).
          {
            typet op_t = operands_tc[idx].type();
            if(is_reference(op_t))
              op_t = to_reference_type(op_t).base_type();
            const typet &base_t = struct_type.bases()[b].type();
            if(
              op_t.id() == ID_struct_tag && base_t.id() == ID_struct_tag &&
              (to_struct_tag_type(op_t).get_identifier() ==
                 to_struct_tag_type(base_t).get_identifier() ||
               subtype_typecast(
                 follow_tag(to_struct_tag_type(op_t)),
                 follow_tag(to_struct_tag_type(base_t)))))
            {
              typet clean_base_t = base_t;
              clean_base_t.remove(ID_C_base_name);
              address_of_exprt obj_addr(object_tc);
              typecast_exprt base_ptr(obj_addr, pointer_type(clean_base_t));
              dereference_exprt base_lval(base_ptr);
              base_lval.set(ID_C_lvalue, true);
              exprt val = typecast_exprt::conditional_cast(
                operands_tc[idx], clean_base_t);
              side_effect_expr_assignt assign(
                std::move(base_lval), std::move(val), typet(), source_location);
              typecheck_side_effect_assignment(assign);
              block.add(code_expressiont(std::move(assign)));
              ++idx;
              continue;
            }
          }

          // Collect from_base data members belonging to this base
          exprt::operandst base_ops;
          if(operands_tc[idx].id() == ID_initializer_list)
            base_ops = operands_tc[idx].operands();
          else
            base_ops.push_back(operands_tc[idx]);
          std::size_t bidx = 0;
          for(const auto &comp : struct_type.components())
          {
            if(
              !comp.get_bool(ID_from_base) || comp.get_bool(ID_is_type) ||
              comp.get_bool(ID_is_static) || comp.type().id() == ID_code)
              continue;
            if(bidx >= base_ops.size())
              break;
            member_exprt member(object_tc, comp.get_name(), comp.type());
            member.set(ID_C_lvalue, true);
            exprt val =
              typecast_exprt::conditional_cast(base_ops[bidx], comp.type());
            side_effect_expr_assignt assign(
              std::move(member), std::move(val), typet(), source_location);
            typecheck_side_effect_assignment(assign);
            block.add(code_expressiont(std::move(assign)));
            ++bidx;
          }
          ++idx;
        }
        // Initialize non-static data members
        for(const auto &comp : struct_type.components())
        {
          if(
            comp.get_bool(ID_from_base) || comp.get_bool(ID_is_type) ||
            comp.get_bool(ID_is_static) || comp.type().id() == ID_code)
            continue;
          member_exprt member(object_tc, comp.get_name(), comp.type());
          member.set(ID_C_lvalue, true);
          exprt val;
          if(idx < operands_tc.size())
          {
            // N5008 [dcl.init.aggr]/4.2 + [dcl.init.ref]: a REFERENCE
            // element is BOUND to its initializer, not assigned through.
            if(is_reference(comp.type()))
            {
              val = operands_tc[idx];
              reference_initializer(val, to_reference_type(comp.type()));
            }
            else
            {
            // look through an already_typechecked wrapper (nil-typed)
            const exprt &op_probe =
              operands_tc[idx].id() == ID_already_typechecked
                ? to_unary_expr(operands_tc[idx]).op()
                : operands_tc[idx];
            if(
              comp.type().id() == ID_array &&
              (op_probe.id() == ID_initializer_list ||
               op_probe.type().id() == ID_array ||
               to_array_type(comp.type()).size().is_constant()))
            {
              // N5008 [dcl.init.aggr]/4.2: an ARRAY element is itself
              // aggregate-initialized, element-wise -- arrays are not
              // assignable, so the assignment below would be rejected
              // ("direct assignments to arrays not permitted"; the
              // shape of a default member initializer `vec v_{{7,8}};`
              // whose member contains an array).  Recurse: a braced
              // list contributes its elements, an already-typed array
              // VALUE is copied element-wise by the array branch (it
              // requires the #array_ini tag).
              exprt array_member = member;
              already_typechecked_exprt::make_already_typechecked(
                array_member);
              exprt::operandst elem_ops;
              if(op_probe.id() == ID_initializer_list)
              {
                for(const auto &el : op_probe.operands())
                  elem_ops.push_back(already_typechecked_exprt{el});
              }
              else if(op_probe.type().id() == ID_array)
              {
                exprt aval = op_probe;
                aval.set(ID_C_array_ini, true);
                elem_ops.push_back(already_typechecked_exprt{aval});
              }
              else
              {
                // N5008 [dcl.init.aggr]/16 (brace elision): the
                // initializer list of the SUBAGGREGATE was elided; the
                // array element consumes the next N operands.
                const auto n = numeric_cast_v<std::size_t>(
                  to_constant_expr(to_array_type(comp.type()).size()));
                for(std::size_t k = 0; k < n && idx < operands_tc.size();
                    ++k, ++idx)
                {
                  elem_ops.push_back(
                    already_typechecked_exprt{operands_tc[idx]});
                }
                --idx; // the shared ++idx below advances past the last
              }
              auto elem_call =
                cpp_constructor(source_location, array_member, elem_ops);
              if(elem_call.has_value())
                block.add(std::move(*elem_call));
              ++idx;
              continue;
            }
              val = typecast_exprt::conditional_cast(
                operands_tc[idx], comp.type());
            }
            ++idx;
          }
          else
          {
            // N5008 [dcl.init.aggr]/5: an aggregate element without an
            // explicit initializer is initialized from its default
            // member initializer or copy-initialized from {} --
            // value-initialization, approximated by zero
            // initialization.  Previously trailing members were left
            // uninitialized, so `aggt x(1, 2)` with three members read
            // garbage from the third.
            if(comp.get_base_name() == "@most_derived")
              val = from_integer(1, comp.type());
            else
            {
              const auto zero = ::zero_initializer(
                comp.type(), source_location, namespacet{symbol_table});
              if(!zero.has_value())
                continue;
              val = *zero;
            }
          }
          side_effect_expr_assignt assign(
            std::move(member), std::move(val), typet(), source_location);
          typecheck_side_effect_assignment(assign);
          block.add(code_expressiont(std::move(assign)));
        }
        return std::move(block);
      }
    }

    // set most-derived bits
    code_blockt block;
    for(const auto &component : struct_type.components())
    {
      if(component.get_base_name() != "@most_derived")
        continue;

      member_exprt member(object_tc, component.get_name(), component.type());
      member.add_source_location() = source_location;
      member.set(ID_C_lvalue, object_tc.get_bool(ID_C_lvalue));

      // the flag is a c_bool (see cpp_typecheck_bases.cpp)
      exprt val = from_integer(
        component.get_bool(ID_from_base) ? 0 : 1, component.type());

      side_effect_expr_assignt assign(
        std::move(member), std::move(val), typet(), source_location);

      typecheck_side_effect_assignment(assign);

      block.add(code_expressiont(std::move(assign)));
    }

    // enter struct scope
    cpp_save_scopet save_scope(cpp_scopes);
    // Constructor overload resolution below runs with the current scope
    // moved into the class; record the caller's scope as the point of
    // use so accessibility of argument conversions -- in particular
    // derived-to-base conversions relying on FRIENDSHIP of the caller
    // ([class.access.base]/4) -- is judged from here.  Restored
    // alongside the scope itself.
    struct access_scope_guardt
    {
      cpp_typecheckt &tc;
      cpp_scopet *saved;
      explicit access_scope_guardt(cpp_typecheckt &t)
        : tc(t), saved(t.access_judgment_scope)
      {
        tc.access_judgment_scope = t.cpp_scopes.current_scope_ptr;
      }
      ~access_scope_guardt()
      {
        tc.access_judgment_scope = saved;
      }
    } access_scope_guard{*this};
    cpp_scopes.set_scope(struct_type.get(ID_name));

    // find name of constructor
    const struct_typet::componentst &components = struct_type.components();

    irep_idt constructor_name;

    for(const auto &c : components)
    {
      const typet &type = c.type();

      if(
        !c.get_bool(ID_from_base) && type.id() == ID_code &&
        to_code_type(type).return_type().id() == ID_constructor)
      {
        constructor_name = c.get_base_name();
        break;
      }
    }

    if(constructor_name.empty())
    {
      // [class.default.ctor]: a defaulted default constructor
      // zero-initializes all members. If the type has no explicit
      // constructor (e.g., template instantiation where the
      // "= default" constructor was not elaborated), fall through
      // to zero-initialization instead of reporting an error.
      if(operands.empty())
      {
        // Default construction with no arguments — treat as
        // zero-initialization (same as "= default" semantics).
        return code_expressiont{
          side_effect_expr_nondett{object.type(), source_location}};
      }
      // N5008 [class.ctor.general]/[temp.inst]: the type is non-POD and is
      // being constructed with arguments, but no constructor is present as a
      // component of this struct type.  This happens when the target type's
      // constructors have not been materialised as components at the point an
      // out-of-line / deferred member-function body is type-checked -- e.g.
      // constructing std::filesystem::path from a std::string inside
      // `T::~T()`, where the string->path converting-constructor conversion is
      // computed while type-checking the deferred destructor body and path's
      // constructor components are not yet visible there.  A constructor is
      // named after its class ([class.ctor.general]/1); since the class scope
      // has already been entered above, resolve the constructor by the class's
      // own name.  Overload resolution in that scope finds the constructors,
      // including constructor *templates* (never stored as plain components),
      // instantiating the matching one.  If the class genuinely has no usable
      // constructor the call below fails with the ordinary "no match".
      if(object_tc.type().id() == ID_struct_tag)
      {
        const symbolt &tag_symbol =
          lookup(to_struct_tag_type(object_tc.type()));
        constructor_name = tag_symbol.base_name;
      }
    }

    if(constructor_name.empty())
    {
      error().source_location = source_location;
      error() << "non-POD type has no constructor" << eom;
      throw 0;
    }

    side_effect_expr_function_callt function_call(
      cpp_namet(constructor_name, source_location).as_expr(),
      operands_tc,
      uninitialized_typet(),
      source_location);

    typecheck_side_effect_function_call(function_call);

    if(function_call.get(ID_statement) != ID_temporary_object)
    {
      error().source_location = source_location;
      error() << "constructor call did not resolve to temporary object" << eom;
      throw 0;
    }

    exprt &initializer =
      static_cast<exprt &>(function_call.add(ID_initializer));

    DATA_INVARIANT(
      initializer.id() == ID_code &&
        initializer.get(ID_statement) == ID_expression,
      "initializer must be expression statement");

    auto &statement_expr = to_code_expression(to_code(initializer));

    side_effect_expr_function_callt &func_ini =
      to_side_effect_expr_function_call(statement_expr.expression());

    exprt &tmp_this = func_ini.arguments().front();
    if(
      tmp_this.id() == ID_typecast &&
      to_typecast_expr(tmp_this).op().id() == ID_address_of)
    {
      // An INHERITED constructor ([class.inhctor.init]/1): the temporary
      // is typed D but the selected base constructor takes B* -- the
      // materialization wrapped `this` in a derived-to-base conversion
      // ([conv.ptr]/3).  Rebind the underlying address to the real object,
      // keeping the conversion.
      exprt &inner = to_typecast_expr(tmp_this).op();
      DATA_INVARIANT(
        to_address_of_expr(inner).object().id() == ID_new_object,
        "expected new_object operand in address_of expression");
      inner = address_of_exprt(object_tc);
    }
    else
    {
      DATA_INVARIANT(
        to_address_of_expr(tmp_this).object().id() == ID_new_object,
        "expected new_object operand in address_of expression");

      tmp_this = address_of_exprt(object_tc);
    }

    const auto &initializer_code = to_code(initializer);

    if(block.statements().empty())
      return initializer_code;
    else
    {
      block.add(initializer_code);
      return std::move(block);
    }
  }
  else
    UNREACHABLE;

  return {};
}

void cpp_typecheckt::new_temporary(
  const source_locationt &source_location,
  const typet &type,
  const exprt::operandst &ops,
  exprt &temporary)
{
  // create temporary object
  side_effect_exprt tmp_object_expr(ID_temporary_object, type, source_location);
  tmp_object_expr.set(ID_mode, ID_cpp);

  exprt new_object(ID_new_object);
  new_object.add_source_location() = tmp_object_expr.source_location();
  new_object.set(ID_C_lvalue, true);
  new_object.type() = tmp_object_expr.type();

  already_typechecked_exprt::make_already_typechecked(new_object);

  auto new_code = cpp_constructor(source_location, new_object, ops);

  if(new_code.has_value())
  {
    if(new_code->get_statement() == ID_assign)
      tmp_object_expr.add_to_operands(std::move(new_code->op1()));
    else
      tmp_object_expr.add(ID_initializer) = *new_code;
  }

  temporary.swap(tmp_object_expr);
}

void cpp_typecheckt::new_temporary(
  const source_locationt &source_location,
  const typet &type,
  const exprt &op,
  exprt &temporary)
{
  exprt::operandst ops;
  ops.push_back(op);
  new_temporary(source_location, type, ops, temporary);
}
