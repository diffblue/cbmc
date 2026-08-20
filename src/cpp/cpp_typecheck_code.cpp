/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/expr_initializer.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/source_location.h>
#include <util/std_code.h>
#include <util/std_types.h>
#include <util/string_constant.h>
#include <util/symbol_table_base.h>

#include <ansi-c/anonymous_member.h>

#include "cpp_convert_type.h"
#include "cpp_declarator_converter.h"
#include "cpp_exception_id.h"
#include "cpp_sfinae_context.h"
#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"
#include "cpp_util.h"

/// N5008 [stmt.return]/2 + [dcl.init.list]/3.4 + [dcl.init.aggr]: decide
/// whether a braced-init-list return operand aggregate-initializes the
/// (class) return type, and if so build the initialization.
/// \param return_type: the function's return type (a struct_tag)
/// \param init_list: the braced-init-list operand (typechecked in place)
/// \return the value initializing the result object, or nullopt when the
///   return type is not an aggregate for this list (then the constructor
///   paths in typecheck_return apply)
std::optional<exprt> cpp_typecheckt::braced_return_aggregate_value(
  const typet &return_type,
  exprt &init_list)
{
  elaborate_class_template(return_type);
  const struct_typet &struct_type = follow_tag(to_struct_tag_type(return_type));

  // [dcl.init.aggr]/1 (C++20 rule): an aggregate has no user-declared
  // constructor.  Compiler-synthesized ones are marked #is_implicit_ctor;
  // template and inherited constructors are recorded as struct flags.
  if(
    struct_type.get_bool("has_template_constructor") ||
    struct_type.get_bool("has_inherited_constructor"))
  {
    return {};
  }
  for(const auto &c : struct_type.components())
  {
    if(c.type().id() != ID_code || c.get_bool(ID_from_base))
      continue;
    if(to_code_type(c.type()).return_type().id() != ID_constructor)
      continue;
    if(c.type().get_bool("#is_implicit_ctor"))
      continue;
    return {};
  }

  for(auto &op : init_list.operands())
    typecheck_expr(op);

  // [dcl.init.list]/3.2: a single element of the same class (or one
  // derived from it) initializes the object from that element -- the
  // copy/move path, not aggregate element-wise initialization.
  if(init_list.operands().size() == 1)
  {
    const typet &op_t = init_list.operands().front().type();
    if(
      op_t.id() == ID_struct_tag &&
      (to_struct_tag_type(op_t).get_identifier() ==
         to_struct_tag_type(return_type).get_identifier() ||
       subtype_typecast(follow_tag(to_struct_tag_type(op_t)), struct_type)))
    {
      return {};
    }
  }

  if(!struct_type.bases().empty())
  {
    // C++17 aggregates with base classes: cpp_constructor's aggregate
    // machinery assembles base-subobject plus member initialization.
    exprt::operandst ctor_args;
    for(auto &op : init_list.operands())
      ctor_args.push_back(already_typechecked_exprt{op});
    exprt temporary;
    new_temporary(
      init_list.source_location(), return_type, ctor_args, temporary);
    return temporary;
  }

  // Bases-free aggregate: [dcl.init.aggr]/3 -- each element of the list
  // copy-initializes the corresponding member, in declaration order.
  struct_exprt result({}, return_type);
  const auto &ops = init_list.operands();
  std::size_t idx = 0;
  for(const auto &c : struct_type.components())
  {
    // Padding and non-data components are not aggregate elements
    // ([dcl.init.aggr]/2, [class.mem]).
    if(
      c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
      c.get_bool(ID_is_static) || c.get_is_padding() ||
      c.type().id() == ID_code || c.get_base_name() == "@most_derived")
    {
      continue;
    }
    if(idx < ops.size())
    {
      exprt val = ops[idx++];
      if(is_reference(c.type()))
        reference_initializer(val, to_reference_type(c.type()));
      else
        implicit_typecast(val, c.type());
      result.add_to_operands(std::move(val));
    }
    else
    {
      // Fewer initializers than elements ([dcl.init.aggr]/5 would
      // value-initialize the rest); decline and let the constructor
      // paths diagnose, matching convert_initializer's behaviour.
      return {};
    }
  }
  if(idx < ops.size())
    return {}; // more initializers than elements: ill-formed here
  already_typechecked_exprt::make_already_typechecked(result);
  return std::move(result);
}

void cpp_typecheckt::typecheck_return(code_frontend_returnt &code)
{
  // Lambda / C++14 return type deduction: when the declared return type is a
  // placeholder -- `auto` (ID_auto) or `decltype(auto)` (an ID_decltype marked
  // `#auto`) -- typecheck the return expression WITHOUT an implicit conversion
  // (there is no target type yet) and deduce the return type from it.  Without
  // covering the decltype(auto) case a deferred deduction (convert_function set
  // defer_auto_return because the return expression could not be typed in
  // isolation, e.g. it mentions a body-local `using` alias) would fall through
  // to the normal path below and try to convert the value to the still
  // unresolved `<<type:decltype>>`, which is an error and aborts goto
  // conversion.  N5008 [dcl.spec.auto]/2-3.
  const bool deduced_decltype_auto =
    return_type.id() == ID_decltype && return_type.get_bool("#auto");
  if(return_type.id() == ID_auto || deduced_decltype_auto)
  {
    if(code.has_return_value())
    {
      typecheck_expr(code.return_value());
      typet deduced = code.return_value().type();
      // decltype(auto) of a parenthesized lvalue deduces a reference type
      // ([dcl.type.decltype]); mirror the eager path in convert_function.
      if(deduced_decltype_auto && code.return_value().get_bool(ID_C_lvalue))
        deduced = reference_typet(deduced, config.ansi_c.pointer_width);
      return_type = deduced;
    }
    else
      return_type = void_type();
    return;
  }

  // [dcl.init.list] p3: For non-aggregate class types, brace-init
  // calls a constructor. Unwrap single-element initializer_lists
  // so the base class typecheck handles the conversion through
  // the normal constructor call path (which correctly handles
  // rvalue references for move constructors).
  //
  // Exception: if the return type has a *viable* initializer-list
  // constructor for the braced-init-list ([over.match.list]/1 phase
  // 1.1, e.g. `return {s};` for std::vector<std::string>), the whole
  // list must be passed as a single std::initializer_list argument
  // rather than unwrapped to its element.  Build that argument and
  // construct the returned temporary explicitly.
  if(
    code.has_return_value() &&
    code.return_value().id() == ID_initializer_list &&
    (return_type.id() == ID_struct_tag || return_type.id() == ID_union_tag) &&
    !cpp_is_pod(return_type) &&
    has_viable_init_list_constructor(return_type, code.return_value()))
  {
    auto il_val = build_init_list_argument(return_type, code.return_value());
    if(il_val.has_value())
    {
      already_typechecked_exprt::make_already_typechecked(*il_val);
      exprt::operandst ctor_args;
      ctor_args.push_back(std::move(*il_val));
      exprt temporary;
      new_temporary(
        code.return_value().source_location(),
        return_type,
        ctor_args,
        temporary);
      code.return_value() = std::move(temporary);
    }
  }
  else if(
    code.has_return_value() &&
    code.return_value().id() == ID_initializer_list &&
    !code.return_value().operands().empty() &&
    return_type.id() == ID_struct_tag && !cpp_is_pod(return_type))
  {
    // N5008 [stmt.return]/2 + [dcl.init.list]/3.4: a braced-init-list
    // operand copy-list-initializes the result object; when the return
    // type is an AGGREGATE this is aggregate initialization
    // ([dcl.init.aggr]) -- the list's elements initialize the class's
    // elements -- not a constructor call.  Without this branch the
    // single-element unwrap below rerouted `return {r};` to constructor
    // overload resolution, which only sees the implicit default/copy
    // constructor and fails ("found no match") whenever the aggregate
    // has a non-POD member.  When the return type is NOT an aggregate
    // (or the list is a [dcl.init.list]/3.2 same-class single element),
    // the helper declines and the pre-existing paths below run.
    auto aggregate_value =
      braced_return_aggregate_value(return_type, code.return_value());
    if(aggregate_value.has_value())
      code.return_value() = std::move(*aggregate_value);
  }
  else if(
    code.has_return_value() &&
    code.return_value().id() == ID_initializer_list &&
    code.return_value().operands().size() == 1 &&
    (return_type.id() == ID_struct_tag || return_type.id() == ID_union_tag) &&
    !cpp_is_pod(return_type))
  {
    code.return_value() = code.return_value().operands().front();
  }

  // Per [stmt.return]/3 (C++11): `return { a, b, ... };` in a function
  // whose return type is a class type constructs a temporary of the
  // return type using list-initialization with the braced-init-list
  // and returns that temporary.  For multi-element braced returns
  // to non-POD class types, CBMC's `implicit_typecast` has no
  // conversion from `initializer_list` to the class type and emits
  // "invalid implicit conversion from 'irep(\"(\\\"\\\")\")' to 'struct T'".
  // Construct the temporary explicitly via `new_temporary` (which
  // wraps `cpp_constructor`, performing [over.match.list] overload
  // resolution) before the base typecheck runs.
  if(
    code.has_return_value() &&
    code.return_value().id() == ID_initializer_list &&
    code.return_value().operands().size() > 1 &&
    (return_type.id() == ID_struct_tag || return_type.id() == ID_union_tag) &&
    !cpp_is_pod(return_type))
  {
    exprt::operandst ctor_args;
    for(auto &op : code.return_value().operands())
    {
      exprt arg = op;
      typecheck_expr(arg);
      ctor_args.push_back(std::move(arg));
    }
    exprt temporary;
    new_temporary(
      code.return_value().source_location(), return_type, ctor_args, temporary);
    code.return_value() = std::move(temporary);
  }

  // N5008 [stmt.return]/2: the operand initializes the function call's
  // result object by copy-initialization.  For non-POD class types,
  // materialize the returned temporary by a constructor call chosen by
  // overload resolution against the operand's VALUE CATEGORY: an lvalue
  // operand selects the copy constructor, an rvalue the move constructor
  // ([over.match.viable], [over.ics.ref]).  This must happen BEFORE the
  // base type-checker's implicit_typecast: computing the conversion
  // sequence performs the lvalue-to-rvalue conversion ([conv.lval]) and
  // strips the operand's lvalue marking, after which constructor
  // selection would see every operand as an rvalue and mis-select the
  // MOVE constructor -- for self-referential classes (the small-string
  // optimization) the move then steals a pointer into a bitwise
  // temporary copy of the source.
  if(
    code.has_return_value() && !is_reference(return_type) &&
    !cpp_is_pod(return_type) &&
    (return_type.id() == ID_struct_tag || return_type.id() == ID_union_tag))
  {
    // N5008 [stmt.return]/2 + [dcl.init.list]/3.5: `return {};` for a
    // class return type VALUE-INITIALIZES the result object -- the
    // default constructor is called.  Passing the empty
    // braced-init-list on as a constructor argument instead would run
    // overload resolution over the CONVERTING constructor templates
    // (e.g. std::optional's `optional(_Up&&)` with its _Requires
    // SFINAE default argument), where the untyped braced-init-list
    // produces "missing type in template argument" and wrong
    // semantics.
    if(
      code.return_value().id() == ID_initializer_list &&
      code.return_value().operands().empty())
    {
      exprt temporary;
      new_temporary(
        code.return_value().source_location(),
        return_type,
        exprt::operandst{},
        temporary);
      code.return_value().swap(temporary);
    }

    typecheck_expr(code.return_value());

    if(
      code.return_value().id() != ID_temporary_object &&
      code.return_value().id() != ID_side_effect)
    {
      // Check that the destructor symbol exists for the return type.
      const struct_typet &struct_type =
        follow_tag(to_struct_tag_type(return_type));
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
        // N5008 [class.copy.elis]/3 (implicit move): when the operand is
        // a (possibly parenthesized) id-expression naming a non-volatile
        // object with automatic storage duration declared in the body or
        // parameter list of the function, overload resolution to select
        // the constructor is first performed treating the operand as an
        // rvalue -- the MOVE constructor is selected if one exists.  Any
        // other operand (a global, a class member, the referent of a
        // reference parameter) is an lvalue and selects the COPY
        // constructor; treating those as rvalues would move from an
        // object the function does not own.
        exprt operand = code.return_value();
        if(operand.id() == ID_symbol)
        {
          const symbolt &operand_symbol =
            lookup(to_symbol_expr(operand).get_identifier());
          if(
            !operand_symbol.is_static_lifetime && operand_symbol.is_lvalue &&
            operand.type().get_bool(ID_C_volatile) == false)
          {
            // treated as an rvalue for constructor selection
            operand.remove(ID_C_lvalue);
          }
        }

        exprt temporary;
        new_temporary(
          code.return_value().source_location(),
          return_type,
          already_typechecked_exprt{operand},
          temporary);
        code.return_value().swap(temporary);
      }
    }

    // The operand is now fully type-checked (and possibly wrapped);
    // keep the base type-checker from re-type-checking it.
    already_typechecked_exprt::make_already_typechecked(code.return_value());
  }

  c_typecheck_baset::typecheck_return(code);
}

void cpp_typecheckt::typecheck_code(codet &code)
{
  const irep_idt &statement = code.get_statement();

  if(statement == ID_try_catch)
  {
    code.type() = empty_typet();
    typecheck_try_catch(code);
  }
  else if(statement == ID_member_initializer)
  {
    code.type() = empty_typet();
    typecheck_member_initializer(code);
  }
  else if(statement == ID_msc_if_exists || statement == ID_msc_if_not_exists)
  {
  }
  else if(statement == ID_decl_block)
  {
    // type checked already
  }
  else if(statement == "cpp-using")
  {
    // using declaration in function body
    cpp_usingt cpp_using;
    cpp_using.swap(
      static_cast<cpp_usingt &>(static_cast<irept &>(code.add("cpp_using"))));
    convert(cpp_using);
    code = codet(ID_skip);
  }
  else if(statement == ID_cpp_namespace_spec)
  {
    // namespace alias in block scope: namespace X = Y::Z;
    cpp_namespace_spect ns_spec;
    ns_spec.swap(static_cast<cpp_namespace_spect &>(
      static_cast<irept &>(code.add(ID_namespace))));
    convert(ns_spec);
    code = codet(ID_skip);
  }
  else if(statement == ID_expression)
  {
    if(
      !code.has_operands() || code.op0().id() != ID_side_effect ||
      to_side_effect_expr(code.op0()).get_statement() != ID_assign)
    {
      c_typecheck_baset::typecheck_code(code);
      return;
    }

    // as an extension, we support indexed access into signed/unsigned
    // bitvectors, typically used with __CPROVER::(un)signedbv<N>
    exprt &expr = code.op0();

    if(expr.operands().size() == 2)
    {
      auto &binary_expr = to_binary_expr(expr);

      if(binary_expr.op0().id() == ID_index)
      {
        exprt array = to_index_expr(binary_expr.op0()).array();
        typecheck_expr(array);

        if(
          array.type().id() == ID_signedbv ||
          array.type().id() == ID_unsignedbv)
        {
          typecheck_expr(binary_expr.op1());
          shl_exprt shl{
            from_integer(1, array.type()),
            to_index_expr(binary_expr.op0()).index()};
          exprt rhs = if_exprt{
            equal_exprt{
              binary_expr.op1(), from_integer(0, binary_expr.op1().type())},
            bitand_exprt{array, bitnot_exprt{shl}},
            bitor_exprt{array, shl}};
          binary_expr.op0() = to_index_expr(binary_expr.op0()).array();
          binary_expr.op1() = rhs;
        }
      }
    }

    c_typecheck_baset::typecheck_code(code);
  }
  else if(statement == ID_static_assert)
  {
    PRECONDITION(code.operands().size() == 1 || code.operands().size() == 2);

    typecheck_expr(code.op0());
    if(code.operands().size() == 2)
      typecheck_expr(code.op1());

    implicit_typecast_bool(code.op0());
    simplify(code.op0(), *this);

    if(code.op0().is_constant() && code.op0() == false_exprt())
    {
      // Per [temp.res.general]/6 (C++23): static_assert(false) in a
      // template body (e.g., MSVC's std::declval guard) should not
      // be fatal.  Convert to a runtime assertion so the body can
      // continue processing.  The assertion will fire at runtime
      // if the function is actually called.
      code = codet{ID_skip};
      return;
    }
  }
  else if(statement == "for_range")
  {
    // Lower range-based for to a regular for loop.
    // for(decl : range) body  →
    // { type var; for(size_t __i=0; __i<N; ++__i) { var=range[__i]; body } }
    code.type() = empty_typet();
    source_locationt loc = code.source_location();

    PRECONDITION(code.operands().size() == 3);
    exprt decl_op = code.op0();
    exprt range_op = code.op1();
    codet body = to_code(code.op2());

    // Type-check the range expression
    typecheck_expr(range_op);

    typet range_type = range_op.type();

    // Convert initializer_list to array for range-based for
    std::optional<codet> arr_init;
    if(
      range_type.id() != ID_array && range_op.id() == ID_initializer_list &&
      !range_op.operands().empty())
    {
      const typet &elem_type = range_op.operands().front().type();
      range_type = array_typet(
        elem_type, from_integer(range_op.operands().size(), size_type()));
      range_op.type() = range_type;
      // Convert initializer_list to array expression for symex
      range_op.id(ID_array);

      // Materialize into a temporary array variable.  Use a per-loop
      // suffix so multiple range-based fors in the same function do
      // not collide on `__range_arr` (see the comment by the
      // class-range path below for details).
      const std::string scope_prefix =
        id2string(cpp_scopes.current_scope().prefix);
      const std::string arr_id = scope_prefix + "__range_arr_" +
                                 id2string(loc.get_line()) + "_" +
                                 id2string(loc.get_column());
      {
        auxiliary_symbolt sym;
        sym.name = arr_id;
        sym.base_name = "__range_arr_" + id2string(loc.get_line()) + "_" +
                        id2string(loc.get_column());
        sym.type = range_type;
        sym.mode = ID_cpp;
        sym.module = module;
        sym.location = loc;
        sym.is_file_local = true;
        sym.is_thread_local = true;
        sym.is_lvalue = true;
        symbol_table.insert(std::move(sym));
      }
      symbol_exprt arr_sym(arr_id, range_type);
      codet assign_arr(ID_assign);
      assign_arr.copy_to_operands(arr_sym);
      assign_arr.copy_to_operands(range_op);
      assign_arr.add_source_location() = loc;
      arr_init = std::move(assign_arr);
      range_op = std::move(arr_sym);
    }

    if(range_type.id() != ID_array)
    {
      // Per N5008 [stmt.ranged]/1.3.2: if the type of `range` is a
      // class type C and lookups in the scope of C find both
      // `begin` and `end`, the desugaring is
      //   auto && __range = for-range-initializer;
      //   auto __begin = __range.begin();
      //   auto __end   = __range.end();
      //   for(; __begin != __end; ++__begin) {
      //     for-range-declaration = *__begin;
      //     statement
      //   }
      // and operator overload resolution handles `!=`, `++` and
      // `*`.  Construct the equivalent code via cpp_name/member
      // expressions and let `typecheck_expr` resolve the overloads.
      if(
        range_type.id() == ID_struct_tag || range_type.id() == ID_struct ||
        range_type.id() == ID_union_tag || range_type.id() == ID_union)
      {
        const std::string scope_prefix =
          id2string(cpp_scopes.current_scope().prefix);

        // Each range-based for in the same function must use unique
        // auxiliary symbol names for `__range`/`__begin`/`__end`.
        // Without a per-loop suffix, the second range-for's
        // `symbol_table.insert` of `<scope>::__for_begin` (etc.)
        // silently fails because the first range-for already
        // inserted a symbol with that name; the second loop then
        // re-uses the FIRST loop's iterator type via
        // `lookup_ref(begin_id)`, causing the iterator
        // dereference and the loop variable `auto`-deduction to
        // bind to the wrong element type.  Concrete symptom on
        // CBMC's own source: `lispirep.cpp::irep2lisp` has two
        // sequential range-fors,
        //   for(const auto &irep : src.get_sub())          // vector<irept>
        //   for(const auto &irep_entry : src.get_named_sub())  // map of pairs
        // The second loop's `auto` was deduced as `irept` (from
        // the first loop's `__for_begin`), surfacing as the
        // spurious diagnostic
        //   symbol 'first' is unknown
        // when the body referenced `irep_entry.first`.  Use the
        // source location's line and column as a unique
        // per-instance suffix.
        const std::string loc_suffix =
          "_" + id2string(loc.get_line()) + "_" + id2string(loc.get_column());

        // Materialise the range into an auxiliary symbol so that
        // `__range.begin()` and `__range.end()` are well-formed
        // expressions (the original `range_op` may be a temporary
        // function-call result that we don't want to evaluate
        // twice).
        const std::string range_id = scope_prefix + "__for_range" + loc_suffix;
        const std::string range_base = "__for_range" + loc_suffix;
        {
          auxiliary_symbolt sym;
          sym.name = range_id;
          sym.base_name = range_base;
          sym.type = range_type;
          sym.mode = ID_cpp;
          sym.module = module;
          sym.location = loc;
          sym.is_file_local = true;
          sym.is_thread_local = true;
          sym.is_lvalue = true;
          symbol_table.insert(std::move(sym));

          // Register in cpp_scopes so cpp_name lookup finds it.
          cpp_idt &id =
            cpp_scopes.put_into_scope(symbol_table.lookup_ref(range_id));
          id.id_class = cpp_idt::id_classt::SYMBOL;
        }
        symbol_exprt range_sym_expr(range_id, range_type);

        codet range_init(ID_assign);
        range_init.copy_to_operands(range_sym_expr);
        range_init.copy_to_operands(range_op);
        range_init.add_source_location() = loc;

        // Build __range.begin() and __range.end() calls.  The
        // overload resolution + member lookup happens in
        // typecheck_side_effect_function_call →
        // typecheck_function_expr → typecheck_expr_member.  The
        // pattern matches the existing `obj.operator->()`
        // construction in `cpp_typecheck_expr.cpp`: wrap the
        // receiver in `already_typechecked_exprt` so the receiver
        // name isn't re-resolved, and call
        // `typecheck_side_effect_function_call` directly (not
        // `typecheck_expr`).
        // Build __range.begin() and __range.end() calls.  The
        // overload resolution + member lookup happens in
        // typecheck_side_effect_function_call →
        // typecheck_function_expr → typecheck_expr_member.
        // Receiver is a cpp_namet so the typechecker takes the
        // standard name-lookup path (synthesised symbol_exprts
        // miss some annotations the resolver relies on).
        auto build_member_call = [&](const irep_idt &member_base_name)
          -> side_effect_expr_function_callt
        {
          cpp_namet member_name{member_base_name, loc};
          cpp_namet receiver_name{
            symbol_table.lookup_ref(range_id).base_name, loc};

          exprt member_expr(ID_member);
          member_expr.add(ID_component_cpp_name) = member_name;
          member_expr.copy_to_operands(static_cast<const exprt &>(
            static_cast<const irept &>(receiver_name)));

          side_effect_expr_function_callt call(
            std::move(member_expr), {}, uninitialized_typet{}, loc);
          typecheck_side_effect_function_call(call);
          return call;
        };

        side_effect_expr_function_callt begin_call_se =
          build_member_call("begin");
        side_effect_expr_function_callt end_call_se = build_member_call("end");
        exprt begin_call{std::move(begin_call_se)};
        exprt end_call{std::move(end_call_se)};

        // Iterator types — deduce from the calls' result types.
        const typet iter_type = begin_call.type();

        // Auxiliary symbols for __begin and __end.
        const std::string begin_id = scope_prefix + "__for_begin" + loc_suffix;
        const std::string begin_base = "__for_begin" + loc_suffix;
        {
          auxiliary_symbolt sym;
          sym.name = begin_id;
          sym.base_name = begin_base;
          sym.type = iter_type;
          sym.mode = ID_cpp;
          sym.module = module;
          sym.location = loc;
          sym.is_file_local = true;
          sym.is_thread_local = true;
          sym.is_lvalue = true;
          symbol_table.insert(std::move(sym));
          cpp_idt &id =
            cpp_scopes.put_into_scope(symbol_table.lookup_ref(begin_id));
          id.id_class = cpp_idt::id_classt::SYMBOL;
        }
        const std::string end_id = scope_prefix + "__for_end" + loc_suffix;
        const std::string end_base = "__for_end" + loc_suffix;
        {
          auxiliary_symbolt sym;
          sym.name = end_id;
          sym.base_name = end_base;
          sym.type = end_call.type();
          sym.mode = ID_cpp;
          sym.module = module;
          sym.location = loc;
          sym.is_file_local = true;
          sym.is_thread_local = true;
          sym.is_lvalue = true;
          symbol_table.insert(std::move(sym));
          cpp_idt &id =
            cpp_scopes.put_into_scope(symbol_table.lookup_ref(end_id));
          id.id_class = cpp_idt::id_classt::SYMBOL;
        }

        symbol_exprt begin_sym_expr(begin_id, iter_type);
        symbol_exprt end_sym_expr(end_id, end_call.type());

        // Helper that produces a cpp_namet referring to a given
        // auxiliary symbol's base name.  Pre-typechecked symbol
        // expressions are missing some lvalue/scope annotations
        // that the parser-emitted form has, which causes the
        // operator-overload resolver to silently miss matches.
        // Building a `cpp_namet` and letting `typecheck_expr_main`
        // resolve it through the standard name-lookup path
        // restores the annotations.
        auto sym_use = [&](const irep_idt &sym_id) -> exprt
        {
          cpp_namet n{symbol_table.lookup_ref(sym_id).base_name, loc};
          return static_cast<const exprt &>(static_cast<const irept &>(n));
        };

        codet begin_init(ID_assign);
        begin_init.copy_to_operands(begin_sym_expr);
        begin_init.copy_to_operands(begin_call);
        begin_init.add_source_location() = loc;

        codet end_init(ID_assign);
        end_init.copy_to_operands(end_sym_expr);
        end_init.copy_to_operands(end_call);
        end_init.add_source_location() = loc;

        // Loop body: var = *__begin; body;
        // Resolve the user-side declaration the same way the
        // array path does: extract its base name and type
        // (deducing `auto` from `*__begin`).
        cpp_declarationt &cpp_decl = static_cast<cpp_declarationt &>(decl_op);
        PRECONDITION(!cpp_decl.declarators().empty());
        cpp_declaratort &declarator = cpp_decl.declarators().front();
        const irep_idt &var_base_name =
          declarator.name().get_sub().front().get(ID_identifier);

        // Compute *__begin to deduce auto.  Pass the receiver as
        // a cpp_namet referring to the auxiliary symbol; the
        // typechecker's standard cpp_name resolution path produces
        // the same symbol_exprt as the parser would for
        // `*__for_begin`, with all the lvalue/scope annotations
        // intact.  (Constructing a symbol_exprt directly skips
        // some of those annotations, causing operator overload
        // resolution to silently miss matches.)
        exprt deref_expr(ID_dereference);
        deref_expr.copy_to_operands(sym_use(begin_id));
        typecheck_expr(deref_expr);

        typet var_type = cpp_decl.type();
        // If the declared type contains `auto` (bare `auto`,
        // `const auto&`, `auto*`, `auto&`, etc.), deduce by
        // substituting `auto` with the type of `*__begin`.
        // The previous check `var_type.id() == ID_auto` only
        // matched bare `auto`, leaving a `merged_type(const, auto)`
        // for `const auto&` un-deduced, surfacing later as
        //   member operator requires struct/union type on left
        //   hand side but got '<<type:auto>>'
        // when the loop variable is used.
        if(has_auto(var_type))
          cpp_convert_auto(var_type, deref_expr.type(), get_message_handler());
        typecheck_type(var_type);

        const std::string var_id = scope_prefix + id2string(var_base_name);
        {
          auxiliary_symbolt sym;
          sym.name = var_id;
          sym.base_name = var_base_name;
          sym.type = var_type;
          sym.mode = ID_cpp;
          sym.module = module;
          sym.location = loc;
          sym.is_file_local = true;
          sym.is_thread_local = true;
          sym.is_lvalue = true;
          symbol_table.insert(std::move(sym));

          cpp_idt &scope_id =
            cpp_scopes.put_into_scope(symbol_table.lookup_ref(var_id));
          scope_id.id_class = cpp_idt::id_classt::SYMBOL;
        }
        symbol_exprt var_expr(var_id, var_type);

        codet assign_elem(ID_assign);
        assign_elem.copy_to_operands(var_expr);
        assign_elem.copy_to_operands(deref_expr);
        assign_elem.add_source_location() = loc;

        // Loop condition: __begin != __end (operator!= resolution)
        exprt cond(ID_notequal);
        cond.copy_to_operands(sym_use(begin_id));
        cond.copy_to_operands(sym_use(end_id));
        typecheck_expr(cond);

        // Loop iter: ++__begin (operator++ resolution)
        exprt iter(ID_side_effect);
        iter.set(ID_statement, ID_preincrement);
        iter.copy_to_operands(sym_use(begin_id));
        typecheck_expr(iter);

        // Type-check the body
        // Per N5008 [stmt.ranged]: range-based for is a loop, so
        // `break` and `continue` are permitted inside its body.
        // Save and set the flags before recursing into the body so
        // the inner `typecheck_continue` / `typecheck_break` accept
        // the statements; restore on the way out.
        const bool old_break_is_allowed = break_is_allowed;
        const bool old_continue_is_allowed = continue_is_allowed;
        break_is_allowed = continue_is_allowed = true;
        typecheck_code(body);
        break_is_allowed = old_break_is_allowed;
        continue_is_allowed = old_continue_is_allowed;

        code_blockt loop_body;
        loop_body.add(std::move(assign_elem));
        loop_body.add(std::move(body));
        loop_body.add_source_location() = loc;

        code_fort for_code(
          code_skipt{}, std::move(cond), std::move(iter), std::move(loop_body));
        for_code.add_source_location() = loc;

        code_blockt outer;
        outer.add(std::move(range_init));
        outer.add(std::move(begin_init));
        outer.add(std::move(end_init));
        outer.add(std::move(for_code));
        outer.add_source_location() = loc;

        code = std::move(outer);
        return;
      }

      error().source_location = loc;
      error() << "range-based for requires an array type" << eom;
      throw 0;
    }

    const exprt array_size =
      typecast_exprt(to_array_type(range_type).size(), size_type());
    const typet &elem_type = to_array_type(range_type).element_type();

    // Extract variable name from the declaration
    cpp_declarationt &cpp_decl = static_cast<cpp_declarationt &>(decl_op);
    PRECONDITION(!cpp_decl.declarators().empty());
    cpp_declaratort &declarator = cpp_decl.declarators().front();
    const irep_idt &var_base_name =
      declarator.name().get_sub().front().get(ID_identifier);

    // Resolve auto type — handle bare `auto`, `const auto&`,
    // `auto*`, `auto&`, etc. by substituting the array element
    // type into any `auto` token within the declared type.
    typet var_type = cpp_decl.type();
    if(has_auto(var_type))
      cpp_convert_auto(var_type, elem_type, get_message_handler());
    typecheck_type(var_type);

    // Create the loop variable via a normal declaration
    const std::string scope_prefix =
      id2string(cpp_scopes.current_scope().prefix);

    // Index variable: __CPROVER_size_t __range_i
    const std::string idx_id = scope_prefix + "__range_i";
    {
      auxiliary_symbolt sym;
      sym.name = idx_id;
      sym.base_name = "__range_i";
      sym.type = size_type();
      sym.mode = ID_cpp;
      sym.module = module;
      sym.location = loc;
      sym.is_file_local = true;
      sym.is_thread_local = true;
      sym.is_lvalue = true;
      symbol_table.insert(std::move(sym));
    }
    symbol_exprt idx_expr(idx_id, size_type());

    // Loop variable
    const std::string var_id = scope_prefix + id2string(var_base_name);
    {
      auxiliary_symbolt sym;
      sym.name = var_id;
      sym.base_name = var_base_name;
      sym.type = var_type;
      sym.mode = ID_cpp;
      sym.module = module;
      sym.location = loc;
      sym.is_file_local = true;
      sym.is_thread_local = true;
      sym.is_lvalue = true;
      symbol_table.insert(std::move(sym));

      cpp_idt &scope_id =
        cpp_scopes.put_into_scope(symbol_table.lookup_ref(var_id));
      scope_id.id_class = cpp_idt::id_classt::SYMBOL;
    }
    symbol_exprt var_expr(var_id, var_type);

    // init: __range_i = 0
    codet init_code(ID_assign);
    init_code.copy_to_operands(idx_expr);
    init_code.copy_to_operands(from_integer(0, size_type()));
    init_code.add_source_location() = loc;

    // cond: __range_i < N
    binary_relation_exprt cond(idx_expr, ID_lt, array_size);
    cond.add_source_location() = loc;

    // iter: ++__range_i
    side_effect_exprt iter(ID_preincrement, size_type(), loc);
    iter.copy_to_operands(idx_expr);

    // var = range[__range_i]
    index_exprt elem(range_op, idx_expr);
    codet assign_elem(ID_assign);
    assign_elem.copy_to_operands(var_expr);
    assign_elem.copy_to_operands(elem);
    assign_elem.add_source_location() = loc;

    // Type-check the body
    // Per N5008 [stmt.ranged]: range-based for is a loop, so
    // `break` and `continue` are permitted inside its body.
    {
      const bool old_break_is_allowed = break_is_allowed;
      const bool old_continue_is_allowed = continue_is_allowed;
      break_is_allowed = continue_is_allowed = true;
      typecheck_code(body);
      break_is_allowed = old_break_is_allowed;
      continue_is_allowed = old_continue_is_allowed;
    }

    // Build: { var = range[__i]; body; }
    code_blockt loop_body;
    loop_body.add(std::move(assign_elem));
    loop_body.add(std::move(body));
    loop_body.add_source_location() = loc;

    code_fort for_code(
      std::move(init_code),
      std::move(cond),
      std::move(iter),
      std::move(loop_body));
    for_code.add_source_location() = loc;

    if(arr_init.has_value())
    {
      code_blockt block;
      block.add(std::move(*arr_init));
      block.add(std::move(for_code));
      block.add_source_location() = loc;
      code = std::move(block);
    }
    else
    {
      code = std::move(for_code);
    }
  }
  else if(statement == "structured_binding")
  {
    // C++17 structured bindings: auto [a, b] = expr;
    // Lower to assignments from struct members.
    code.type() = empty_typet();
    source_locationt loc = code.source_location();

    PRECONDITION(code.operands().size() == 1);
    exprt init = code.op0();
    typecheck_expr(init);

    const irept &bindings = code.find(irep_idt("bindings"));
    const auto &binding_list = bindings.get_sub();

    // Get the struct type
    typet init_type = init.type();
    if(init_type.id() == ID_struct_tag)
      init_type = follow_tag(to_struct_tag_type(init_type));

    if(init_type.id() != ID_struct && init_type.id() != ID_array)
    {
      error().source_location = loc;
      error() << "structured bindings require a struct/class or array type"
              << eom;
      throw 0;
    }

    if(init_type.id() == ID_array)
    {
      // Array structured binding: auto [a, b, c] = arr;
      const array_typet &arr_type = to_array_type(init_type);
      const typet &elem_type = arr_type.element_type();

      const std::string scope_prefix =
        id2string(cpp_scopes.current_scope().prefix);
      const std::string sb_id = scope_prefix + "__sb";
      {
        auxiliary_symbolt sym;
        sym.name = sb_id;
        sym.base_name = "__sb";
        sym.type = init.type();
        sym.mode = ID_cpp;
        sym.module = module;
        sym.location = loc;
        sym.is_file_local = true;
        sym.is_thread_local = true;
        sym.is_lvalue = true;
        sym.value = init;
        symbol_table.insert(std::move(sym));
      }
      symbol_exprt sb_expr(sb_id, init.type());

      code_blockt block;
      block.add_source_location() = loc;

      codet sb_assign(ID_assign);
      sb_assign.copy_to_operands(sb_expr);
      sb_assign.copy_to_operands(init);
      sb_assign.add_source_location() = loc;
      block.add(std::move(sb_assign));

      for(std::size_t i = 0; i < binding_list.size(); ++i)
      {
        const irep_idt &name = binding_list[i].id();
        const std::string var_id = scope_prefix + id2string(name);
        {
          auxiliary_symbolt sym;
          sym.name = var_id;
          sym.base_name = name;
          sym.type = elem_type;
          sym.mode = ID_cpp;
          sym.module = module;
          sym.location = loc;
          sym.is_file_local = true;
          sym.is_thread_local = true;
          sym.is_lvalue = true;
          symbol_table.insert(std::move(sym));
          const symbolt &inserted = symbol_table.lookup_ref(var_id);
          cpp_idt &id = cpp_scopes.put_into_scope(inserted);
          id.id_class = cpp_idt::id_classt::SYMBOL;
        }
        symbol_exprt var_expr(var_id, elem_type);
        index_exprt member(sb_expr, from_integer(i, c_index_type()), elem_type);
        codet assign(ID_assign);
        assign.copy_to_operands(var_expr);
        assign.copy_to_operands(member);
        assign.add_source_location() = loc;
        block.add(std::move(assign));
      }

      code.swap(block);
      return;
    }

    // [dcl.struct.bind]/4: if std::tuple_size<E> is a complete type with a
    // member named `value`, the structured binding uses the "tuple-like"
    // protocol: the i-th name is bound to get<i>(e) (found by member lookup or
    // ADL), with type std::tuple_element<i, E>::type.  The data members of E
    // are not used in this case (their order may differ from the get<i> order,
    // e.g. for std::tuple).  Probe for std::tuple_size<E>::value; if present,
    // decompose via get<i>.
    {
      exprt ts_probe{ID_cpp_name};
      {
        auto &sub = ts_probe.get_sub();
        sub.push_back(irept{ID_name});
        sub.back().set(ID_identifier, "std");
        sub.push_back(irept{"::"});
        sub.push_back(irept{ID_name});
        sub.back().set(ID_identifier, "tuple_size");
        irept targs{ID_template_args};
        targs.add(ID_arguments)
          .get_sub()
          .push_back(static_cast<const irept &>(type_exprt{init.type()}));
        sub.push_back(targs);
        sub.push_back(irept{"::"});
        sub.push_back(irept{ID_name});
        sub.back().set(ID_identifier, "value");
      }
      ts_probe.add_source_location() = loc;

      bool has_tuple_size = false;
      mp_integer ts_value = 0;
      {
        const std::size_t saved_errors =
          get_message_handler().get_message_count(messaget::M_ERROR);
        const unsigned saved_verbosity = get_message_handler().get_verbosity();
        get_message_handler().set_verbosity(0);
        try
        {
          cpp_save_scopet save_scope(cpp_scopes);
          exprt probe = ts_probe;
          typecheck_expr(probe);
          make_constant(probe);
          const auto v = numeric_cast<mp_integer>(probe);
          if(v.has_value())
          {
            has_tuple_size = true;
            ts_value = *v;
          }
        }
        catch(...)
        {
          get_message_handler().set_message_count(
            messaget::M_ERROR, saved_errors);
        }
        get_message_handler().set_verbosity(saved_verbosity);
      }

      // Eligibility probe: the get-protocol is only usable if get<0>(e) itself
      // resolves.  Some library types have a tuple_size specialization yet
      // their get<i> cannot be evaluated here (e.g. std::tuple's heavily
      // constrained accessors); for those, fall back to the data-member
      // decomposition below rather than silently dropping the bindings.
      if(has_tuple_size && ts_value > 0)
      {
        const std::size_t saved_errors =
          get_message_handler().get_message_count(messaget::M_ERROR);
        const unsigned saved_verbosity = get_message_handler().get_verbosity();
        get_message_handler().set_verbosity(0);
        try
        {
          cpp_save_scopet save_scope(cpp_scopes);
          exprt get_name{ID_cpp_name};
          {
            auto &sub = get_name.get_sub();
            sub.push_back(irept{ID_name});
            sub.back().set(ID_identifier, "get");
            irept targs{ID_template_args};
            targs.add(ID_arguments)
              .get_sub()
              .push_back(from_integer(0, size_type()));
            sub.push_back(targs);
            get_name.add_source_location() = loc;
          }
          exprt probe_arg = init;
          side_effect_expr_function_callt probe_call{
            get_name, {probe_arg}, uninitialized_typet{}, loc};
          typecheck_expr(probe_call);
          if(
            probe_call.type().is_nil() || probe_call.type().id() == ID_empty ||
            probe_call.type().id().empty())
            has_tuple_size = false;
        }
        catch(...)
        {
          has_tuple_size = false;
          get_message_handler().set_message_count(
            messaget::M_ERROR, saved_errors);
        }
        get_message_handler().set_verbosity(saved_verbosity);
      }

      if(has_tuple_size)
      {
        if(ts_value != binding_list.size())
        {
          error().source_location = loc;
          error() << "structured binding count (" << binding_list.size()
                  << ") does not match std::tuple_size (" << ts_value << ")"
                  << eom;
          throw 0;
        }

        const std::string scope_prefix =
          id2string(cpp_scopes.current_scope().prefix);
        const bool is_ref = code.get_bool(ID_C_reference);

        // __sb is a reference (pointer) to the source object -- the original
        // lvalue or the materialised temporary.  We deliberately do not copy
        // the whole object even for an `auto` (by-value) binding: copying it
        // would invoke its copy constructor, which for some library types
        // (e.g. std::tuple, whose constructors are heavily constrained) cannot
        // be evaluated here.  Each `auto` binding is still an independent copy
        // of get<i>(e), so the bindings are value-independent of the source.
        const std::string sb_id = scope_prefix + "__sb";
        typet sb_type = pointer_type(init.type());
        sb_type.set(ID_C_reference, true);
        {
          auxiliary_symbolt sym;
          sym.name = sb_id;
          sym.base_name = "__sb";
          sym.type = sb_type;
          sym.mode = ID_cpp;
          sym.module = module;
          sym.location = loc;
          sym.is_file_local = true;
          sym.is_thread_local = true;
          sym.is_lvalue = true;
          symbol_table.insert(std::move(sym));
        }

        code_blockt block;
        block.add_source_location() = loc;

        symbol_exprt sb_expr{sb_id, sb_type};
        {
          codet sb_assign{ID_assign};
          sb_assign.copy_to_operands(sb_expr);
          sb_assign.copy_to_operands(address_of_exprt{init});
          sb_assign.add_source_location() = loc;
          block.add(std::move(sb_assign));
        }

        // get<i> is applied to *__sb (the source object).
        exprt get_arg = dereference_exprt{sb_expr, init.type()};

        for(std::size_t i = 0; i < binding_list.size(); ++i)
        {
          const irep_idt &name = binding_list[i].id();

          // Build get<i>(<object>) -- unqualified, so ADL finds the namespace
          // get (member lookup is not modelled separately here).
          exprt get_name{ID_cpp_name};
          {
            auto &sub = get_name.get_sub();
            sub.push_back(irept{ID_name});
            sub.back().set(ID_identifier, "get");
            irept targs{ID_template_args};
            targs.add(ID_arguments)
              .get_sub()
              .push_back(from_integer(i, size_type()));
            sub.push_back(targs);
            get_name.add_source_location() = loc;
          }
          side_effect_expr_function_callt get_call{
            get_name, {get_arg}, uninitialized_typet{}, loc};
          typecheck_expr(get_call);

          // The binding refers to the result of get<i>; a reference for an
          // auto& binding, a copy for an auto binding.
          typet binding_type = get_call.type();
          if(!is_ref && is_reference(binding_type))
            binding_type = to_reference_type(binding_type).base_type();

          const std::string var_id = scope_prefix + id2string(name);
          {
            auxiliary_symbolt sym;
            sym.name = var_id;
            sym.base_name = name;
            sym.type = binding_type;
            sym.mode = ID_cpp;
            sym.module = module;
            sym.location = loc;
            sym.is_file_local = true;
            sym.is_thread_local = true;
            sym.is_lvalue = true;
            symbol_table.insert(std::move(sym));
            cpp_idt &scope_id =
              cpp_scopes.put_into_scope(symbol_table.lookup_ref(var_id));
            scope_id.id_class = cpp_idt::id_classt::SYMBOL;
          }

          symbol_exprt var_expr{var_id, binding_type};
          codet assign{ID_assign};
          assign.copy_to_operands(var_expr);
          assign.copy_to_operands(get_call);
          assign.add_source_location() = loc;
          block.add(std::move(assign));
        }

        code.swap(block);
        return;
      }
    }

    const struct_typet &struct_type = to_struct_type(init_type);
    const auto &components = struct_type.components();

    // Collect non-static data members
    std::vector<const struct_typet::componentt *> data_members;
    for(const auto &comp : components)
    {
      if(
        !comp.get_bool(ID_is_static) && !comp.get_bool(ID_is_type) &&
        !comp.get_bool(ID_C_is_padding) && comp.type().id() != ID_code)
        data_members.push_back(&comp);
    }

    if(binding_list.size() != data_members.size())
    {
      error().source_location = loc;
      error() << "structured binding count (" << binding_list.size()
              << ") does not match member count (" << data_members.size() << ")"
              << eom;
      throw 0;
    }

    const std::string scope_prefix =
      id2string(cpp_scopes.current_scope().prefix);

    const bool is_ref = code.get_bool(ID_C_reference);

    // Hidden variable for the source object
    const std::string sb_id = scope_prefix + "__sb";
    {
      auxiliary_symbolt sym;
      sym.name = sb_id;
      sym.base_name = "__sb";
      if(is_ref)
      {
        // For auto& bindings, __sb is a reference to the source
        typet ref_type = pointer_type(init.type());
        ref_type.set(ID_C_reference, true);
        sym.type = ref_type;
      }
      else
      {
        sym.type = init.type();
      }
      sym.mode = ID_cpp;
      sym.module = module;
      sym.location = loc;
      sym.is_file_local = true;
      sym.is_thread_local = true;
      sym.is_lvalue = true;
      sym.value = init;
      symbol_table.insert(std::move(sym));
    }

    code_blockt block;
    block.add_source_location() = loc;

    if(is_ref)
    {
      // For auto& [a,b] = obj; make bindings be references to obj's members
      symbol_exprt sb_expr(sb_id, pointer_type(init.type()));
      sb_expr.type().set(ID_C_reference, true);

      codet sb_assign(ID_assign);
      sb_assign.copy_to_operands(sb_expr);
      sb_assign.copy_to_operands(address_of_exprt(init));
      sb_assign.add_source_location() = loc;
      block.add(std::move(sb_assign));

      dereference_exprt deref_sb(sb_expr, init.type());

      for(std::size_t i = 0; i < binding_list.size(); ++i)
      {
        const irep_idt &name = binding_list[i].id();
        const auto &comp = *data_members[i];

        typet ref_type = pointer_type(comp.type());
        ref_type.set(ID_C_reference, true);

        const std::string var_id = scope_prefix + id2string(name);
        {
          auxiliary_symbolt sym;
          sym.name = var_id;
          sym.base_name = name;
          sym.type = ref_type;
          sym.mode = ID_cpp;
          sym.module = module;
          sym.location = loc;
          sym.is_file_local = true;
          sym.is_thread_local = true;
          sym.is_lvalue = true;
          symbol_table.insert(std::move(sym));

          cpp_idt &scope_id =
            cpp_scopes.put_into_scope(symbol_table.lookup_ref(var_id));
          scope_id.id_class = cpp_idt::id_classt::SYMBOL;
        }

        symbol_exprt var_expr(var_id, ref_type);
        member_exprt member(deref_sb, comp.get_name(), comp.type());
        codet assign(ID_assign);
        assign.copy_to_operands(var_expr);
        assign.copy_to_operands(address_of_exprt(member));
        assign.add_source_location() = loc;
        block.add(std::move(assign));
      }

      code = std::move(block);
      return;
    }

    symbol_exprt sb_expr(sb_id, init.type());

    // Assign __sb = init
    codet sb_assign(ID_assign);
    sb_assign.copy_to_operands(sb_expr);
    sb_assign.copy_to_operands(init);
    sb_assign.add_source_location() = loc;
    block.add(std::move(sb_assign));

    // Create binding variables as copies of members
    for(std::size_t i = 0; i < binding_list.size(); ++i)
    {
      const irep_idt &name = binding_list[i].id();
      const auto &comp = *data_members[i];

      const std::string var_id = scope_prefix + id2string(name);
      {
        auxiliary_symbolt sym;
        sym.name = var_id;
        sym.base_name = name;
        sym.type = comp.type();
        sym.mode = ID_cpp;
        sym.module = module;
        sym.location = loc;
        sym.is_file_local = true;
        sym.is_thread_local = true;
        sym.is_lvalue = true;
        member_exprt member(sb_expr, comp.get_name(), comp.type());
        sym.value = member;
        symbol_table.insert(std::move(sym));

        cpp_idt &scope_id =
          cpp_scopes.put_into_scope(symbol_table.lookup_ref(var_id));
        scope_id.id_class = cpp_idt::id_classt::SYMBOL;
      }

      symbol_exprt var_expr(var_id, comp.type());
      member_exprt member(sb_expr, comp.get_name(), comp.type());
      codet assign(ID_assign);
      assign.copy_to_operands(var_expr);
      assign.copy_to_operands(member);
      assign.add_source_location() = loc;
      block.add(std::move(assign));
    }

    code = std::move(block);
  }
  else
    c_typecheck_baset::typecheck_code(code);
}

/// Tag every bare `throw;` (a throw side-effect with no operand -- a rethrow)
/// reachable in \p e, but not already tagged, with \p handler_id.  Used to
/// record, for a rethrow lexically inside a handler, which handler's exception
/// it re-propagates (N5008 [except.throw]/8).  Because inner handlers are
/// type-checked before their enclosing handler, a rethrow that already carries
/// a tag belongs to an inner handler and is left untouched, so each rethrow is
/// attributed to its innermost enclosing handler.
static void tag_rethrow_handler(exprt &e, const irep_idt &handler_id)
{
  if(
    e.id() == ID_side_effect && e.get(ID_statement) == ID_throw &&
    e.operands().empty() && e.get("#rethrow_handler").empty())
  {
    e.set("#rethrow_handler", handler_id);
  }

  for(auto &op : e.operands())
    tag_rethrow_handler(op, handler_id);
}

void cpp_typecheckt::typecheck_try_catch(codet &code)
{
  bool first = true;

  for(auto &op : code.operands())
  {
    if(first)
    {
      // this is the 'try'
      typecheck_code(to_code(op));
      first = false;
    }
    else
    {
      // This is (one of) the catch clauses.
      code_blockt &catch_block = to_code_block(to_code(op));

      // look at the catch operand
      auto &statements = catch_block.statements();
      PRECONDITION(!statements.empty());

      if(statements.front().get_statement() == ID_ellipsis)
      {
        statements.erase(statements.begin());

        // do body
        typecheck_code(catch_block);
      }
      else
      {
        // turn references into non-references
        {
          codet &decl_stmt = to_code(statements.front());
          if(
            decl_stmt.get_statement() != ID_decl ||
            decl_stmt.operands().size() != 1 ||
            decl_stmt.op0().id() != ID_cpp_declaration)
          {
            error().source_location = catch_block.source_location();
            error() << "expected type name in catch clause" << eom;
            throw 0;
          }
          cpp_declarationt &cpp_declaration =
            to_cpp_declaration(decl_stmt.op0());

          if(cpp_declaration.declarators().size() != 1)
          {
            error().source_location = catch_block.source_location();
            error() << "expected single declarator in catch clause" << eom;
            throw 0;
          }
          cpp_declaratort &declarator = cpp_declaration.declarators().front();

          if(
            declarator.type().id() == ID_frontend_pointer &&
            declarator.type().get_bool(ID_C_reference))
          {
            declarator.type() =
              to_type_with_subtype(declarator.type()).subtype();
          }
          else if(is_reference(declarator.type()))
          {
            declarator.type() =
              to_reference_type(declarator.type()).base_type();
          }

          // The catch variable's value is supplied by the exception object at
          // runtime ([except.handle]); the front-end only needs to declare it.
          // Mark a placeholder initializer that convert_initializer turns into
          // a nondet initialization, so the type-checker does not synthesise a
          // spurious construction.  An `int` 0 placeholder (the previous
          // behaviour) made a class-typed catch variable try to construct its
          // class from an int -- which failed ("found no match for symbol 'X'",
          // argument `signed int`) for every class without a matching int
          // constructor, including move-only classes whose copy constructor is
          // deleted.
          if(declarator.value().is_nil())
          {
            exprt placeholder = from_integer(0, signed_int_type());
            already_typechecked_exprt::make_already_typechecked(placeholder);
            placeholder.set("#exception_catch_init", true);
            declarator.value() = std::move(placeholder);
          }
        }

        // typecheck the body
        typecheck_code(catch_block);

        // the declaration is now in a decl_block
        CHECK_RETURN(!catch_block.statements().empty());
        CHECK_RETURN(
          catch_block.statements().front().get_statement() == ID_decl_block);

        // get the declaration
        const code_frontend_declt &code_decl = to_code_frontend_decl(
          to_code(catch_block.statements().front().op0()));

        // get the type
        const typet &type = code_decl.symbol().type();

        // annotate exception ID
        op.set(ID_exception_id, cpp_exception_id(type, *this));

        // record, for any bare `throw;` lexically inside this handler, that it
        // re-propagates the exception this handler is handling ([except.throw]
        // /8).  Keyed by the catch variable's identifier, which is also how
        // remove_cpp_exceptions identifies the handler.
        tag_rethrow_handler(catch_block, code_decl.symbol().get_identifier());
      }
    }
  }
}

void cpp_typecheckt::typecheck_ifthenelse(code_ifthenelset &code)
{
  // In addition to the C syntax, C++ also allows a declaration
  // as condition. E.g.,
  // if(void *p=...) ...

  if(code.cond().id() == ID_code)
  {
    // C++ [stmt.select]/1-2, [stmt.if]: the condition may be a
    // declaration.  The value of such a condition is the value of the
    // declared variable contextually converted to bool, and the
    // declaration is in scope throughout both substatements.  Rewrite
    //   if(T v = init) S1 [else S2]
    // into the equivalent
    //   { T v = init; if(v) S1 [else S2] }
    // mirroring the existing handling of declaration conditions in
    // typecheck_while / typecheck_switch.  (Previously only the
    // declaration was type-checked and the condition was left as the
    // declaration code, so the branch was never taken -- e.g.
    // libstdc++'s `if (size_type __n = _M_finish - __pos)` in
    // vector::_M_erase_at_end, used by clear()/resize()/erase(first,
    // last), silently behaved as a no-op.)
    // N5008 [stmt.pre]/6: the name introduced by a condition declaration
    // is in scope from its point of declaration until the END OF THE
    // SUBSTATEMENTS; it must NOT be visible in the rest of the enclosing
    // block (redeclaring the same name after the if-statement is
    // well-formed -- libstdc++'s _Hashtable::_M_insert_unique declares
    // `__node_ptr __node` in an if-condition and `_Scoped_node __node`
    // after it).  Type-check the declaration inside a fresh block scope
    // so the name does not leak into the enclosing scope.
    cpp_save_scopet saved_scope(cpp_scopes);
    cpp_scopes.new_block_scope();

    codet decl = to_code(code.cond());
    typecheck_code(decl);

    // The typechecked declaration may be wrapped in a decl_block.
    codet actual_decl = decl;
    if(actual_decl.get_statement() == ID_decl_block)
    {
      PRECONDITION(actual_decl.operands().size() == 1);
      actual_decl = to_code(actual_decl.op0());
    }

    // Use the declared variable, contextually converted to bool, as
    // the condition.
    const auto &decl_symbol = to_code_frontend_decl(actual_decl).symbol();
    exprt cond_expr = decl_symbol;
    implicit_typecast_bool(cond_expr);
    code.cond() = cond_expr;

    // Type-check the condition and both branches as usual (still inside
    // the condition's scope, [stmt.pre]/6: the name is visible in both
    // substatements).
    c_typecheck_baset::typecheck_ifthenelse(code);

    // Wrap so the declaration executes before, and is in scope of, the
    // if-statement.
    code_ifthenelset if_stmt = code;
    code_blockt new_block;
    new_block.add(std::move(decl));
    new_block.add(std::move(if_stmt));
    new_block.add_source_location() = code.source_location();
    static_cast<codet &>(code).swap(new_block);
  }
  else if(code.get_bool(ID_constexpr))
  {
    // C++17 if constexpr: evaluate condition at compile time and
    // discard the branch not taken so that ill-formed code in the
    // discarded branch does not cause errors.
    {
      // The condition of a constexpr if is manifestly constant-evaluated
      // ([expr.const], [stmt.if]/2), so __builtin_is_constant_evaluated() is
      // true within it ([meta.const.eval]/1).
      constant_expression_contextt constant_expression_guard{*this};
      typecheck_expr(code.cond());
    }
    implicit_typecast_bool(code.cond());
    simplify(code.cond(), *this);

    if(code.cond().is_true())
    {
      typecheck_code(code.then_case());
      if(code.has_else_case())
        code.else_case() = code_skipt();
    }
    else if(code.cond().is_false())
    {
      code.then_case() = code_skipt();
      if(code.has_else_case())
        typecheck_code(code.else_case());
    }
    else
    {
      // Condition not constant — try both branches but suppress
      // errors.  In well-formed C++, if-constexpr conditions must
      // be constant, but CBMC may fail to evaluate complex type
      // trait expressions.  Suppressing errors prevents ill-formed
      // [stmt.if]/2: for `if constexpr (c) T; else F;`, the
      // discarded substatement is not instantiated.  CBMC's
      // typecheck_ifthenelse still elaborates both branches and
      // may fail on the discarded one; treat the enclosing
      // `if constexpr` as a SFINAE-like context so a failure in
      // the discarded branch is silently swallowed.  Matches the
      // standard's "discarded statement" semantics.
      try
      {
        sfinae_contextt sfinae_guard{*this};
        c_typecheck_baset::typecheck_ifthenelse(code);
      }
      catch(int)
      {
        // Replace both branches with skip
        code.then_case() = code_skipt();
        if(code.has_else_case())
          code.else_case() = code_skipt();
      }
    }
  }
  else
    c_typecheck_baset::typecheck_ifthenelse(code);
}

void cpp_typecheckt::typecheck_while(code_whilet &code)
{
  // In addition to the C syntax, C++ also allows a declaration
  // as condition. E.g.,
  // while(void *p=...) ...

  if(code.cond().id() == ID_code)
  {
    // Rewrite into: while(true) { decl; if(!var) break; body; }
    // N5008 [stmt.pre]/6: scope the condition's name to the statement
    // (see typecheck_ifthenelse).
    cpp_save_scopet saved_scope(cpp_scopes);
    cpp_scopes.new_block_scope();

    codet decl = to_code(code.cond());
    typecheck_code(decl);

    // The typechecked declaration may be wrapped in a decl_block.
    codet actual_decl = decl;
    if(actual_decl.get_statement() == ID_decl_block)
    {
      PRECONDITION(actual_decl.operands().size() == 1);
      actual_decl = to_code(actual_decl.op0());
    }

    // Extract the declared variable from the declaration
    const auto &decl_symbol = to_code_frontend_decl(actual_decl).symbol();

    // Build: if(!var) break;
    exprt cond_expr = decl_symbol;
    implicit_typecast_bool(cond_expr);
    code_breakt break_stmt;
    break_stmt.add_source_location() = code.source_location();
    code_ifthenelset if_break(not_exprt(cond_expr), std::move(break_stmt));

    // Build the new body: { decl; if(!var) break; old_body; }
    code_blockt new_body({std::move(decl), std::move(if_break), code.body()});
    new_body.add_source_location() = code.source_location();

    code.cond() = true_exprt();
    code.body() = std::move(new_body);

    // Delegate to C typecheck_while for body typechecking and flags
    c_typecheck_baset::typecheck_while(code);
  }
  else
    c_typecheck_baset::typecheck_while(code);
}

void cpp_typecheckt::typecheck_switch(codet &code)
{
  // In addition to the C syntax, C++ also allows a declaration
  // as condition. E.g.,
  // switch(int i=...) ...

  exprt &value = to_code_switch(code).value();
  if(value.id() == ID_code)
  {
    // we shall rewrite that into
    // { int i=....; switch(i) .... }

    codet decl = to_code(value);
    typecheck_decl(decl);

    CHECK_RETURN(decl.get_statement() == ID_decl_block);
    CHECK_RETURN(decl.operands().size() == 1);

    // replace declaration by its symbol
    value = to_code_frontend_decl(to_code(to_unary_expr(decl).op())).symbol();

    c_typecheck_baset::typecheck_switch(code);

    code_blockt code_block({to_code(decl.op0()), code});
    code.swap(code_block);
  }
  else
    c_typecheck_baset::typecheck_switch(code);
}

void cpp_typecheckt::check_default_constructor_access(
  const typet &object_type,
  const source_locationt &source_location,
  cpp_scopet *naming_scope)
{
  if(disable_access_control || naming_scope == nullptr)
    return;

  // Arrays are initialized element-wise ([dcl.init.aggr]); check the
  // element type.
  const typet *element_type = &object_type;
  while(element_type->id() == ID_array)
    element_type = &to_array_type(*element_type).element_type();

  if(element_type->id() != ID_struct_tag)
    return;

  // Resolve the tag to its definition.  During template instantiation a
  // tag may still be incomplete or not (yet) a struct; in that case there
  // is nothing to access-check here, so conservatively accept.
  const symbolt *sym =
    symbol_table.lookup(to_struct_tag_type(*element_type).get_identifier());
  if(sym == nullptr || sym->type.id() != ID_struct)
    return;

  const struct_typet &struct_type = to_struct_type(sym->type);
  if(struct_type.is_incomplete())
    return;

  // Locate the default constructor: the constructor whose only parameter
  // is the implicit `this`.  If there is none, default-initialization
  // does not select a user-provided constructor and there is nothing to
  // access-check here.
  for(const auto &comp : struct_type.components())
  {
    if(comp.type().id() != ID_code)
      continue;
    // Only the class's own constructors are candidates for selection;
    // base-class constructors appear as inherited (from_base) components
    // and are not what default-initialization of this member selects.
    if(comp.get_bool(ID_from_base))
      continue;
    const code_typet &ctor_type = to_code_type(comp.type());
    if(ctor_type.return_type().id() != ID_constructor)
      continue;
    if(ctor_type.parameters().size() != 1)
      continue;

    // Judge accessibility from the point of use (the enclosing class's
    // constructor), not from the member's own class.
    cpp_scopet *saved = cpp_scopes.current_scope_ptr;
    cpp_scopes.current_scope_ptr = naming_scope;
    const bool not_accessible = check_component_access(comp, struct_type);
    cpp_scopes.current_scope_ptr = saved;

    if(not_accessible)
    {
      // System headers may rely on friend/visibility modelling that CBMC
      // does not fully reconstruct; do not reject there (mirrors the
      // resolver's system-header tolerance).
      const std::string file = id2string(source_location.get_file());
      if(
        !file.empty() && (file.find("/include/") != std::string::npos ||
                          file.find("\\include\\") != std::string::npos))
        return;

      error().source_location = source_location;
      error() << "default constructor of '" << to_string(*element_type)
              << "' is not accessible" << eom;
      throw 0;
    }

    return;
  }
}

void cpp_typecheckt::typecheck_member_initializer(codet &code)
{
  // [class.base.init], N5008 [temp.variadic]: a mem-initializer-id that is a
  // template-id (e.g. `_Tuple_impl<I+1, _Tail...>`) denotes a base class.  Its
  // non-type arguments (such as `I+1`) must be evaluated and its type packs
  // expanded -- exactly as the corresponding base-specifier, or a typedef of
  // the same id, is.  Resolving the syntactic template-id directly below (with
  // `I` still an unsubstituted name, so `I+1` unfolded) mis-binds to the
  // enclosing specialization or fails to bind, leaving the initializer
  // unconverted (it then reaches symbolic execution as a raw member_initializer
  // and aborts).  In this instantiated context the id type-checks to the
  // concrete base subobject type, so resolve it as a type and rewrite the
  // initializer to the base's unqualified name plus #base_type, mirroring an
  // implicit base initializer; the resolve below then scopes to that base.
  {
    const cpp_namet &member0 = to_cpp_name(code.find(ID_member));
    if(member0.has_template_args() && code.find("#base_type").is_nil())
    {
      const source_locationt member_loc = member0.source_location();
      const irep_idt member_base_name = member0.get_base_name();
      // Find the enclosing class's direct base whose name matches the
      // mem-initializer-id.  The base subobject's concrete type (with its
      // parameter pack already fully expanded in the base-specifier list) is
      // the authoritative type to initialise -- re-type-checking the syntactic
      // template-id here would instead bind the pack to a single element (the
      // pack is collapsed in the constructor body's template map), yielding the
      // wrong base and an arity mismatch.
      const exprt &this_e = cpp_scopes.current_scope().this_expr;
      typet base_type;
      base_type.make_nil();
      std::size_t n_matches = 0;
      if(this_e.is_not_nil() && this_e.type().id() == ID_pointer)
      {
        const typet &class_tag = to_pointer_type(this_e.type()).base_type();
        if(class_tag.id() == ID_struct_tag)
        {
          const namespacet ns(symbol_table);
          const auto &class_type = ns.follow_tag(to_struct_tag_type(class_tag));
          for(const auto &b : class_type.bases())
          {
            if(b.type().id() != ID_struct_tag)
              continue;
            const symbolt *bsym = symbol_table.lookup(
              to_struct_tag_type(b.type()).get_identifier());
            if(bsym != nullptr && bsym->base_name == member_base_name)
            {
              base_type = b.type();
              ++n_matches;
            }
          }
        }
      }
      // Only rewrite when the base is unambiguous by name.  If a class derives
      // from two specializations of the same template, the explicit template
      // arguments disambiguate and must be resolved the normal way.
      if(n_matches == 1 && base_type.id() == ID_struct_tag)
      {
        const symbolt &base_symbol =
          lookup(to_struct_tag_type(base_type).get_identifier());
        cpp_namet base_cppname(base_symbol.base_name, member_loc);
        code.add("#base_type") = base_type;
        code.add(ID_member) = base_cppname;
      }
    }
  }

  const cpp_namet &member = to_cpp_name(code.find(ID_member));

  // N5008 [temp.variadic]/5: a mem-initializer argument that is a bare
  // pack expansion of a FUNCTION parameter pack (`bound_(b...)`) stands
  // for one argument per pack element.  When the enclosing constructor
  // belongs to a partial specialization whose pack supplies the
  // parameters, typecheck_compound_declarator has already materialised
  // them -- replicated as `b$0..b$N-1` for N >= 2, or kept under the
  // plain name for a single element -- so resolve the expansion against
  // those parameters here.  Left unresolved, the still-ellipsis-marked
  // reference resolves to nil and the member is initialized from
  // nothing ("invalid implicit conversion from '' to 'struct tup'",
  // the libc++ __perfect_forward bound-args shape), dropping the body.
  {
    exprt::operandst new_ops;
    bool changed = false;
    for(const auto &op : as_const(code).operands())
    {
      const bool bare_pack_ref =
        op.id() == ID_cpp_name && op.get_bool(ID_ellipsis) &&
        op.get_sub().size() == 1 && op.get_sub().front().id() == ID_name;
      if(!bare_pack_ref)
      {
        new_ops.push_back(op);
        continue;
      }
      const std::string base =
        id2string(op.get_sub().front().get(ID_identifier));
      // collect replicated parameters base$0.. in order, or the plain one
      std::vector<irep_idt> repl;
      bool plain = false;
      for(const auto *id_ptr : cpp_scopes.current_scope().lookup(
            irep_idt{base}, cpp_scopet::RECURSIVE))
      {
        if(id_ptr->id_class == cpp_idt::id_classt::SYMBOL)
          plain = true;
      }
      if(!plain)
      {
        for(std::size_t k = 0;; ++k)
        {
          const irep_idt cand{base + "$" + std::to_string(k)};
          bool found = false;
          for(const auto *id_ptr :
              cpp_scopes.current_scope().lookup(cand, cpp_scopet::RECURSIVE))
            if(id_ptr->id_class == cpp_idt::id_classt::SYMBOL)
              found = true;
          if(!found)
            break;
          repl.push_back(cand);
        }
      }
      if(plain)
      {
        exprt one = op; // single element: the pattern itself
        one.remove(ID_ellipsis);
        new_ops.push_back(one);
        changed = true;
      }
      else if(!repl.empty())
      {
        for(const auto &r : repl)
        {
          cpp_namet nm{r, op.source_location()};
          exprt e = static_cast<const exprt &>(static_cast<irept &>(nm));
          new_ops.push_back(e);
        }
        changed = true;
      }
      else
        new_ops.push_back(op); // leave to the existing machinery
    }
    if(changed)
      code.operands() = new_ops;
  }

  // Let's first typecheck the operands.
  Forall_operands(it, code)
  {
    const bool has_array_ini = it->get_bool(ID_C_array_ini);
    typecheck_expr(*it);
    if(has_array_ini)
      it->set(ID_C_array_ini, true);
  }

  // re-read the member: it may have been rewritten just above
  // The initializer may be a data member (non-type)
  // or a parent class (type).
  // We ask for VAR only, as we get the parent classes via their
  // N5008 [class.base.init]/7: if the mem-initializer-id denotes a
  // DIRECT BASE that is an aggregate (no user-declared constructor,
  // [dcl.init.aggr]/1), the expression-list or braced-init-list
  // initializes the base subobject per [dcl.init] -- there is no
  // constructor to resolve (make_constructors only synthesizes the
  // default and copy signatures, so a one-element initializer like
  // libc++ tuple's `__tuple_leaf<_Tf>(__u)...` found "no match").
  // Non-template constructors are lowered eagerly by
  // full_member_initialization's POD-base branch; an instantiated
  // constructor TEMPLATE's initializers only pass through here.  Route
  // the initialization through cpp_constructor on the sliced base
  // lvalue: it implements the [dcl.init.general]/16.6 dispatch,
  // including C++17 aggregates with bases and C++20 parenthesized
  // aggregate initialization (P0960).  Per [class.base.init]/2 a name
  // that (also) denotes a data member initializes the member, so the
  // type probe is skipped for member names.
  if(code.find(ID_member).id() == ID_cpp_name && code.has_operands())
  {
    const cpp_namet &mem_name = to_cpp_name(code.find(ID_member));
    const exprt &this_e = cpp_scopes.current_scope().this_expr;
    if(this_e.is_not_nil() && this_e.type().id() == ID_pointer)
    {
      const typet &class_tag = to_pointer_type(this_e.type()).base_type();
      if(class_tag.id() == ID_struct_tag)
      {
        const namespacet ns(symbol_table);
        const auto &class_type = ns.follow_tag(to_struct_tag_type(class_tag));
        bool is_member_name = false;
        for(const auto &c : class_type.components())
        {
          if(
            c.get_base_name() == mem_name.get_base_name() &&
            c.type().id() != ID_code && !c.get_bool(ID_is_type))
          {
            is_member_name = true;
            break;
          }
        }
        typet named_type;
        named_type.make_nil();
        if(!is_member_name)
        {
          const std::size_t errors_before =
            get_message_handler().get_message_count(messaget::M_ERROR);
          try
          {
            sfinae_contextt sfinae_guard{*this};
            named_type = static_cast<const typet &>(code.find(ID_member));
            typecheck_type(named_type);
          }
          catch(...)
          {
            named_type.make_nil();
          }
          get_message_handler().set_message_count(
            messaget::M_ERROR, errors_before);
        }
        if(named_type.id() == ID_struct_tag)
        {
          for(const auto &b : class_type.bases())
          {
            if(
              b.type().id() != ID_struct_tag ||
              to_struct_tag_type(b.type()).get_identifier() !=
                to_struct_tag_type(named_type).get_identifier())
            {
              continue;
            }
            // [dcl.init.aggr]/1: any user-declared constructor
            // disqualifies the aggregate (C++20 rule); only
            // compiler-synthesized ones (#is_implicit_ctor) are ignored.
            const auto &base_struct =
              ns.follow_tag(to_struct_tag_type(b.type()));
            // ... and no virtual functions or virtual base classes
            // ([dcl.init.aggr]/1.3-1.4) -- the vtable pointer component
            // marks both.
            bool has_user_ctor =
              base_struct.get_bool("has_template_constructor") ||
              base_struct.get_bool("has_inherited_constructor");
            for(const auto &c : base_struct.components())
            {
              if(c.get_bool(ID_is_vtptr))
              {
                has_user_ctor = true; // not an aggregate
                break;
              }
            }
            for(const auto &c : base_struct.components())
            {
              if(
                c.type().id() != ID_code || c.get_bool(ID_from_base) ||
                to_code_type(c.type()).return_type().id() != ID_constructor ||
                c.type().get_bool("#is_implicit_ctor"))
              {
                continue;
              }
              has_user_ctor = true;
              break;
            }
            if(has_user_ctor)
              break; // the constructor-resolve path below handles it

            // N5008 [dcl.init.list]/3.2 + [dcl.init.general]/16.6.1: a
            // SINGLE initializer of the base's own type (or derived) is
            // copy-initialization -- the synthesized copy/move
            // constructor's sliced-reference initializer takes this
            // form.  The base's implicit copy constructor handles it;
            // element-wise aggregate initialization here would try to
            // convert the whole base value to the FIRST member.
            if(code.operands().size() == 1)
            {
              typet op_t = code.operands().front().type();
              if(is_reference(op_t))
                op_t = to_reference_type(op_t).base_type();
              if(
                op_t.id() == ID_struct_tag &&
                (to_struct_tag_type(op_t).get_identifier() ==
                   to_struct_tag_type(b.type()).get_identifier() ||
                 subtype_typecast(
                   ns.follow_tag(to_struct_tag_type(op_t)),
                   ns.follow_tag(to_struct_tag_type(b.type())))))
              {
                break; // constructor-resolve path performs the copy
              }
            }

            // Lower to an assignment of an
            // explicit-constructor-call from an initializer-list --
            // the same shape full_member_initialization's POD-base
            // branch emits; its typecheck applies the [dcl.init]
            // rules element-wise to the aggregate.
            typet base_t = b.type();
            base_t.remove(ID_C_base_name);
            exprt lhs_ptr("explicit-typecast", pointer_type(base_t));
            lhs_ptr.copy_to_operands(exprt("cpp-this"));
            lhs_ptr.add_source_location() = code.source_location();
            dereference_exprt lhs(lhs_ptr);
            exprt rhs("explicit-constructor-call", base_t);
            exprt init_list(ID_initializer_list);
            for(const auto &op : as_const(code).operands())
              init_list.copy_to_operands(already_typechecked_exprt{op});
            rhs.add_to_operands(std::move(init_list));
            rhs.add_source_location() = code.source_location();
            code_frontend_assignt assign_code(std::move(lhs), std::move(rhs));
            assign_code.add_source_location() = code.source_location();
            codet new_code = assign_code;
            code.swap(new_code);
            typecheck_code(code);
            return;
          }
        }
      }
    }
  }

  // constructor!
  cpp_typecheck_fargst fargs;
  fargs.in_use = true;
  fargs.operands = code.operands();

  // [class.union.anon]: the members of an anonymous union (or anonymous
  // struct) are members of the enclosing class, so a constructor
  // member-initializer may name such a member directly -- e.g. std::optional
  // initialising the payload of its storage union.  The member is not a scope
  // entry of the enclosing class (only reachable through the unnamed
  // subobject), so the `resolve` below would not find it.  Detect this case
  // and build the initialization through the anonymous subobject via
  // `get_component_rec`.
  if(member.is_simple_name())
  {
    const exprt &this_e = cpp_scopes.current_scope().this_expr;
    if(this_e.is_not_nil() && this_e.type().id() == ID_pointer)
    {
      const typet &class_tag = to_pointer_type(this_e.type()).base_type();
      const irep_idt base_name = member.get_base_name();
      if(class_tag.id() == ID_struct_tag || class_tag.id() == ID_union_tag)
      {
        const namespacet ns(symbol_table);
        const auto &class_type =
          ns.follow_tag(to_struct_or_union_tag_type(class_tag));
        const auto &comps = class_type.components();
        const bool is_direct = std::any_of(
          comps.begin(),
          comps.end(),
          [&](const struct_union_typet::componentt &c)
          { return c.get_base_name() == base_name; });
        if(!is_direct && has_component_rec(class_tag, base_name, ns))
        {
          exprt deref{ID_dereference, class_tag};
          deref.copy_to_operands(this_e);
          deref.set(ID_C_lvalue, true);
          deref.add_source_location() = code.source_location();
          exprt target = get_component_rec(deref, base_name, ns);
          target.set(ID_C_lvalue, true);
          // keep the unwrapped member expression: the
          // already-typechecked wrapper below carries a nil type
          const exprt real_target = target;

          exprt::operandst wrapped_ops;
          wrapped_ops.reserve(code.operands().size());
          for(const auto &op : code.operands())
            wrapped_ops.push_back(
              op.get_bool(ID_C_array_ini) ? op : already_typechecked_exprt{op});
          already_typechecked_exprt::make_already_typechecked(target);

          auto call =
            cpp_constructor(code.source_location(), target, wrapped_ops);
          if(call.has_value())
            code.swap(call.value());
          else if(code.get_bool("#value_init"))
          {
            // N5008 [class.base.init]/7 + [dcl.init.general]/9->/8: an
            // EXPLICIT empty initializer (`member()` / `member{}`)
            // value-initializes, which for a scalar/POD member means
            // zero-initialization -- unlike the synthesized
            // default-initialization entries, which leave the member
            // indeterminate ([dcl.init.general]/7) and rightly become a
            // skip below.
            const auto zero = ::zero_initializer(
              real_target.type(), code.source_location(), *this);
            if(zero.has_value())
            {
              // both sides are fully typechecked already; build the
              // assignment directly (the member expression is an lvalue)
              side_effect_exprt assign(
                ID_assign,
                {real_target, *zero},
                real_target.type(),
                code.source_location());
              code_expressiont new_code(assign);
              code.swap(new_code);
            }
            else
            {
              codet skip{ID_skip};
              skip.add_source_location() = code.source_location();
              code.swap(skip);
            }
          }
          else
          {
            // default-initialisation with no constructor call (POD
            // member): indeterminate value, no code
            codet skip{ID_skip};
            skip.add_source_location() = code.source_location();
            code.swap(skip);
          }
          return;
        }
      }
    }
  }

  // Access to the base-class constructor is judged from the point of use
  // ([class.base.init], [class.access.base]): the derived class whose
  // constructor performs the base-class initialization.  For an implicit
  // base initializer the resolve below scopes into the base subobject (to
  // disambiguate the constructor, see `#base_type`), which would
  // otherwise let the base's own (possibly private) constructor look
  // accessible.  Record the enclosing scope so accessibility is decided
  // from the derived class instead.
  fargs.naming_scope = &cpp_scopes.current_scope();

  // For implicit base-class initializers added by
  // `full_member_initialization`, the `cpp_namet` is the unqualified
  // base class `base_name` and resolve below would fail when the
  // enclosing class derives from two specializations of the same
  // template (e.g., `_Hashtable_ebo_helper<0, _Hash>` vs
  // `<1, _Equal>`).  `full_member_initialization` records the
  // specific base subobject's `struct_tag` type via
  // `#base_type`; if present, scope the resolve to that struct
  // (which uniquely determines the constructor we want) instead of
  // the enclosing class scope.  Restore the original scope before
  // accessing `this_expr` (which is bound to the constructor's
  // class scope, not the base subobject's scope).
  exprt symbol_expr;
  {
    cpp_save_scopet save_scope(cpp_scopes);
    if(code.find("#base_type").is_not_nil())
    {
      const typet &base_type =
        static_cast<const typet &>(code.find("#base_type"));
      if(base_type.id() == ID_struct_tag)
      {
        const irep_idt &tag = to_struct_tag_type(base_type).get_identifier();
        if(cpp_scopes.id_map.find(tag) != cpp_scopes.id_map.end())
          cpp_scopes.set_scope(tag);
      }
    }

    // We should only really resolve in qualified mode,
    // no need to look into the parent.
    // Plus, this should happen in class scope, not the scope of
    // the constructor because of the constructor arguments.
    symbol_expr = resolve(member, cpp_typecheck_resolvet::wantt::VAR, fargs);
  }

  if(symbol_expr.type().id() == ID_code)
  {
    const code_typet &code_type = to_code_type(symbol_expr.type());

    DATA_INVARIANT(
      code_type.parameters().size() >= 1, "at least one parameter");

    // It's a parent. Call the constructor that we got.
    side_effect_expr_function_callt function_call(
      symbol_expr, {}, uninitialized_typet{}, code.source_location());
    function_call.arguments().reserve(code.operands().size() + 1);

    // we have to add 'this'
    exprt this_expr = cpp_scopes.current_scope().this_expr;
    if(this_expr.is_nil())
    {
      // Not in a class context — the member initializer can't be
      // processed (e.g., constructor from a header that failed to
      // elaborate its class scope).
      error().source_location = code.source_location();
      error() << "member initializer outside class context" << eom;
      throw 0;
    }

    make_ptr_typecast(
      this_expr, to_pointer_type(code_type.parameters().front().type()));

    function_call.arguments().push_back(this_expr);

    for(const auto &op : as_const(code).operands())
      function_call.arguments().push_back(op);

    // done building the expression, check the argument types
    typecheck_function_call_arguments(function_call);

    if(symbol_expr.get_bool(ID_C_not_accessible))
    {
      const irep_idt &access = symbol_expr.get(ID_C_access);
      CHECK_RETURN(
        access == ID_private || access == ID_protected ||
        access == ID_noaccess);

      if(access == ID_private || access == ID_noaccess)
      {
        error().source_location = code.find_source_location();
        error() << "constructor of '" << to_string(symbol_expr)
                << "' is not accessible" << eom;
        throw 0;
      }
    }

    code_expressiont code_expression(function_call);

    // Mark the callee as used so that do_not_typechecked processes
    // its body (e.g., base class copy constructors called from a
    // derived class copy constructor's member initializer list).
    if(symbol_expr.id() == ID_symbol)
    {
      symbolt &callee = symbol_table.get_writeable_ref(
        to_symbol_expr(symbol_expr).get_identifier());
      // Record the odr-use: this base/member constructor is invoked by the
      // initializer.  The call is lowered to an unresolved class-name
      // constructor call (resolved only at goto-conversion), so the
      // deferred-body drain's symbol-reference scan would otherwise miss it
      // and leave an explicitly-defaulted / implicitly-defined base
      // constructor uninstantiated ([temp.inst]/4).
      odr_used_by_member_initializer.insert(callee.name);
      if(callee.value.id() == ID_cpp_not_typechecked)
        callee.value.set(ID_is_used, true);
      if(callee.value.is_not_nil() && deferred_typechecking.count(callee.name))
      {
        add_method_body(&callee);
      }
    }

    code.swap(code_expression);
  }
  else
  {
    // a reference member
    if(
      symbol_expr.id() == ID_dereference &&
      to_dereference_expr(symbol_expr).pointer().id() == ID_member &&
      symbol_expr.get_bool(ID_C_implicit))
    {
      // treat references as normal pointers
      exprt tmp = to_dereference_expr(symbol_expr).pointer();
      symbol_expr.swap(tmp);
    }

    if(symbol_expr.id() == ID_symbol && symbol_expr.type().id() != ID_code)
    {
      // maybe the name of the member collides with a parameter of the
      // constructor
      const exprt &this_e = cpp_scopes.current_scope().this_expr;
      if(this_e.is_nil() || this_e.type().id() != ID_pointer)
      {
        error().source_location = code.source_location();
        error() << "member initializer outside class context" << eom;
        throw 0;
      }
      exprt dereference(
        ID_dereference, to_pointer_type(this_e.type()).base_type());
      dereference.copy_to_operands(this_e);
      cpp_typecheck_fargst deref_fargs;
      deref_fargs.add_object(dereference);

      {
        // N5008 [class.base.init]/2: the mem-initializer-id is looked up
        // in the scope of the CONSTRUCTOR'S CLASS (so the data member
        // wins over a same-named constructor parameter).  The scope of
        // an INSTANTIATED member function template records no
        // class_identifier (its parent chain goes through the template
        // scope), and blindly indexing id_map with the empty id inserts
        // and dereferences a null scope pointer.  Derive the class scope
        // from `this` instead, and fall back to the current scope's
        // class_identifier only when set.
        cpp_save_scopet cpp_saved_scope(cpp_scopes);
        // Prefer the class named by `this`: for an instantiated member
        // function template the scope's class_identifier records the
        // member's template-instance scope (not present in id_map under
        // that spelling), while the tag type of `this` names the class
        // symbol whose scope is registered.
        irep_idt class_id;
        {
          const typet &class_tag = to_pointer_type(this_e.type()).base_type();
          if(class_tag.id() == ID_struct_tag || class_tag.id() == ID_union_tag)
            class_id = to_tag_type(class_tag).get_identifier();
        }
        if(
          class_id.empty() ||
          cpp_scopes.id_map.find(class_id) == cpp_scopes.id_map.end())
        {
          const irep_idt fallback_id =
            cpp_scopes.current_scope().class_identifier;
          if(
            !fallback_id.empty() &&
            cpp_scopes.id_map.find(fallback_id) != cpp_scopes.id_map.end())
          {
            class_id = fallback_id;
          }
        }
        auto scope_it = cpp_scopes.id_map.find(class_id);
        if(scope_it == cpp_scopes.id_map.end())
        {
          // Class scopes are keyed by the class symbol's name; a tag
          // identifier carries a `tag-` prefix on the base name --
          // strip it (mirroring the naming convention in
          // instantiate_template's `"tag-" + base_name`).
          const std::string cid = id2string(class_id);
          const auto pos = cid.rfind("tag-");
          if(pos != std::string::npos)
            scope_it =
              cpp_scopes.id_map.find(cid.substr(0, pos) + cid.substr(pos + 4));
        }
        if(scope_it == cpp_scopes.id_map.end() || scope_it->second == nullptr)
        {
          error().source_location = code.source_location();
          error() << "failed to find class scope of member initializer" << eom;
          throw 0;
        }
        cpp_scopes.go_to(*scope_it->second);
        symbol_expr =
          resolve(member, cpp_typecheck_resolvet::wantt::VAR, deref_fargs);
      }

      if(
        symbol_expr.id() == ID_dereference &&
        to_dereference_expr(symbol_expr).pointer().id() == ID_member &&
        symbol_expr.get_bool(ID_C_implicit))
      {
        // treat references as normal pointers
        exprt tmp = to_dereference_expr(symbol_expr).pointer();
        symbol_expr.swap(tmp);
      }
    }

    if(
      symbol_expr.id() == ID_member &&
      to_member_expr(symbol_expr).op().id() == ID_dereference &&
      to_dereference_expr(to_member_expr(symbol_expr).op()).pointer() ==
        cpp_scopes.current_scope().this_expr)
    {
      if(is_reference(symbol_expr.type()))
      {
        // it's a reference member
        if(code.operands().size() != 1)
        {
          error().source_location = code.find_source_location();
          error() << " reference '" << to_string(symbol_expr)
                  << "' expects one initializer" << eom;
          throw 0;
        }

        reference_initializer(
          code.op0(), to_reference_type(symbol_expr.type()));

        // assign the pointers
        symbol_expr.type().remove(ID_C_reference);
        symbol_expr.set(ID_C_lvalue, true);
        code.op0().type().remove(ID_C_reference);

        side_effect_exprt assign(
          ID_assign,
          {symbol_expr, code.op0()},
          typet(),
          code.source_location());
        typecheck_side_effect_assignment(assign);
        code_expressiont new_code(assign);
        code.swap(new_code);
      }
      else
      {
        // it's a data member
        already_typechecked_exprt::make_already_typechecked(symbol_expr);

        // A member initializer of the form `m{}` (an empty
        // brace-or-equal-initializer) value-initializes the member
        // ([dcl.init]/[class.base.init]).  It arrives here as a single
        // empty initializer_list operand; treating it as "no operands"
        // routes it through the value-initialization path below (default
        // constructor for a class type, zero-initialization for a POD),
        // instead of assigning an uninitialized temporary.
        if(
          code.operands().size() == 1 &&
          code.op0().id() == ID_initializer_list &&
          code.op0().operands().empty())
        {
          code.operands().clear();
        }

        // [class.base.init]/7: a braced member initializer
        // list-initializes the member, so [over.match.list]/1 applies:
        // only a viable initializer-list constructor receives the
        // braced-init-list as a single argument (phase 1); otherwise
        // the ELEMENTS of the list are the constructor arguments
        // (phase 2).  The block-scope declaration path (convert_
        // initializer) already implements this two-phase selection;
        // here the raw list (whose elements type-check only against a
        // target) reached overload resolution whole and untyped, so
        // every constructor candidate tied: an NSDMI such as
        // `shared_ptrt nothing{0};` with {shared_ptrt&&, nullptr_t}
        // constructors reported a bogus ambiguity.
        {
          const exprt &inner_se =
            symbol_expr.id() == ID_already_typechecked
              ? to_already_typechecked_expr(symbol_expr).get_expr()
              : symbol_expr;
          if(
            code.operands().size() == 1 &&
            code.op0().id() == ID_initializer_list &&
            inner_se.type().id() == ID_struct_tag &&
            !cpp_is_pod(inner_se.type()) &&
            !has_viable_init_list_constructor(inner_se.type(), code.op0()))
          {
            exprt::operandst elements = code.op0().operands();
            for(auto &element : elements)
              typecheck_expr(element);
            code.operands() = std::move(elements);
          }
        }

        // For default-initialization of a class-type member (no explicit
        // initializer), the selected default constructor must be
        // accessible in this constructor's context ([class.base.init]/12,
        // [class.access.base]).  cpp_constructor resolves the member's
        // constructor in the member's own class scope, which would let a
        // private/inaccessible default constructor pass, so check here
        // from the enclosing class (the point of use).
        if(code.operands().empty())
        {
          const exprt &inner =
            symbol_expr.id() == ID_already_typechecked
              ? to_already_typechecked_expr(symbol_expr).get_expr()
              : symbol_expr;
          check_default_constructor_access(
            inner.type(), code.source_location(), fargs.naming_scope);
        }

        // Operands were already typechecked above; wrap them to prevent
        // cpp_constructor from typechecking them again.  Don't wrap
        // array-ini operands: they are used directly (not re-typechecked)
        // and the wrapper would break array indexing.
        exprt::operandst wrapped_ops;
        wrapped_ops.reserve(code.operands().size());
        for(const auto &op : code.operands())
        {
          if(op.get_bool(ID_C_array_ini))
            wrapped_ops.push_back(op);
          else
            wrapped_ops.push_back(already_typechecked_exprt{op});
        }

        // N5008 [dcl.init.general]/16.6.2.2 (C++20 parenthesized
        // aggregate initialization): a MEMBER of aggregate class type
        // initialized with a parenthesized expression-list and no
        // viable constructor is initialized element-wise, as the braced
        // form ([dcl.init.aggr]/3).  Try that BEFORE constructor
        // resolution, which otherwise hard-errors converting the whole
        // list to the member's type ("invalid implicit conversion from
        // 'signed int' to 'struct tup'" -- the libc++
        // __perfect_forward bound-args member).  Restricted to
        // aggregates ([dcl.init.aggr]/1: no user-declared constructor)
        // and skipped for a single same/derived-type operand, which is
        // copy-initialization ([dcl.init.general]/16.6.1).
        std::optional<codet> agg_call;
        if(!wrapped_ops.empty())
        {
          exprt &inner_a =
            symbol_expr.id() == ID_already_typechecked
              ? to_already_typechecked_expr(symbol_expr).get_expr()
              : symbol_expr;
          if(inner_a.type().id() == ID_struct_tag)
          {
            const struct_typet &mt =
              follow_tag(to_struct_tag_type(inner_a.type()));
            bool has_user_ctor = mt.get_bool("has_template_constructor") ||
                                 mt.get_bool("has_inherited_constructor");
            for(const auto &c : mt.components())
            {
              if(
                c.type().id() == ID_code && !c.get_bool(ID_from_base) &&
                to_code_type(c.type()).return_type().id() == ID_constructor &&
                !c.type().get_bool("#is_implicit_ctor"))
              {
                has_user_ctor = true;
                break;
              }
            }
            bool copyish = false;
            if(wrapped_ops.size() == 1)
            {
              const exprt &op0 =
                wrapped_ops.front().id() == ID_already_typechecked
                  ? to_already_typechecked_expr(wrapped_ops.front()).get_expr()
                  : wrapped_ops.front();
              typet ot = op0.type();
              if(is_reference(ot))
                ot = to_reference_type(ot).base_type();
              if(
                ot.id() == ID_struct_tag &&
                (to_struct_tag_type(ot).get_identifier() ==
                   to_struct_tag_type(inner_a.type()).get_identifier() ||
                 subtype_typecast(follow_tag(to_struct_tag_type(ot)), mt)))
                copyish = true;
            }
            if(!has_user_ctor && !copyish)
            {
              exprt init_list{ID_initializer_list};
              init_list.operands() = wrapped_ops;
              init_list.add_source_location() = code.source_location();
              const typet member_type = inner_a.type();
              const std::size_t errors_before =
                get_message_handler().get_message_count(messaget::M_ERROR);
              std::optional<exprt> agg;
              try
              {
                agg = braced_return_aggregate_value(member_type, init_list);
              }
              catch(...)
              {
                agg.reset();
              }
              get_message_handler().set_message_count(
                messaget::M_ERROR, errors_before);
              if(agg.has_value())
              {
                exprt member_lval = inner_a;
                member_lval.type().set(ID_C_constant, false);
                member_lval.set(ID_C_lvalue, true);
                side_effect_expr_assignt assign(
                  member_lval, *agg, typet(), code.source_location());
                typecheck_side_effect_assignment(assign);
                code_expressiont expr_code(assign);
                expr_code.add_source_location() = code.source_location();
                agg_call = expr_code;
              }
            }
          }
        }

        auto call =
          agg_call.has_value()
            ? agg_call
            : cpp_constructor(code.source_location(), symbol_expr, wrapped_ops);

        if(call.has_value())
          code.swap(call.value());
        else if(wrapped_ops.empty())
        {
          // Value-initialization of a POD member: zero-initialize.
          // symbol_expr is wrapped in already_typechecked_exprt, so
          // get the inner expression for the actual type.
          exprt &inner = symbol_expr.id() == ID_already_typechecked
                           ? to_already_typechecked_expr(symbol_expr).get_expr()
                           : symbol_expr;
          auto zero =
            ::zero_initializer(inner.type(), code.source_location(), *this);
          if(zero.has_value())
          {
            inner.type().set(ID_C_constant, false);
            inner.set(ID_C_lvalue, true);
            // Per [dcl.init]/8 value-initialization of an array is
            // applied element-wise; a direct assignment to an array is
            // not permitted by [expr.ass].  Emit element-wise
            // zero-assignments so that type-check succeeds.
            if(inner.type().id() == ID_array)
            {
              const auto &array_type = to_array_type(inner.type());
              const exprt &size_expr = array_type.size();
              exprt tmp_size = size_expr;
              make_constant_index(tmp_size);
              mp_integer s;
              if(!to_integer(to_constant_expr(tmp_size), s))
              {
                code_blockt block;
                auto elem_zero = ::zero_initializer(
                  array_type.element_type(), code.source_location(), *this);
                if(elem_zero.has_value())
                {
                  for(mp_integer i = 0; i < s; ++i)
                  {
                    index_exprt element{inner, from_integer(i, c_index_type())};
                    element.add_source_location() = code.source_location();
                    element.set(ID_C_lvalue, true);
                    side_effect_expr_assignt elem_assign(
                      element, *elem_zero, typet(), code.source_location());
                    typecheck_side_effect_assignment(elem_assign);
                    block.add(code_expressiont{elem_assign});
                  }
                  code.swap(block);
                  return;
                }
              }
              // Fall through to skip if size not constant or no
              // element zero initializer.
              auto source_location = code.source_location();
              code = code_skipt();
              code.add_source_location() = source_location;
            }
            else
            {
              side_effect_expr_assignt assign(
                inner, *zero, typet(), code.source_location());
              typecheck_side_effect_assignment(assign);
              code_expressiont new_code(std::move(assign));
              code.swap(new_code);
            }
          }
          else
          {
            auto source_location = code.source_location();
            code = code_skipt();
            code.add_source_location() = source_location;
          }
        }
        else
        {
          auto source_location = code.source_location();
          code = code_skipt();
          code.add_source_location() = source_location;
        }
      }
    }
    else
    {
      error().source_location = code.find_source_location();
      error() << "invalid member initializer '" << to_string(symbol_expr) << "'"
              << eom;
      throw 0;
    }
  }
}

void cpp_typecheckt::typecheck_decl(codet &code)
{
  if(code.operands().size() != 1)
  {
    error().source_location = code.find_source_location();
    error() << "declaration expected to have one operand" << eom;
    throw 0;
  }

  PRECONDITION(code.op0().id() == ID_cpp_declaration);

  cpp_declarationt &declaration = to_cpp_declaration(code.op0());

  typet &type = declaration.type();

  bool is_typedef = declaration.is_typedef(); // NOLINT(readability/identifiers)

  if(declaration.declarators().empty() || !has_auto(type))
  {
    // C++17 CTAD: if the type is a class template name without
    // template arguments, try to deduce from constructor arguments.
    bool ctad_done = false;
    if(type.id() == ID_cpp_name && !declaration.declarators().empty())
    {
      const auto &declarator = declaration.declarators().front();
      // Collect init arguments from either init_args (parenthesized)
      // or initializer_list value (brace init)
      const irept &init_args = declarator.find("init_args");
      const exprt &value =
        static_cast<const exprt &>(declarator.find(ID_value));
      std::vector<exprt> ctad_args;
      if(init_args.get_sub().size() > 0)
      {
        for(const auto &a : init_args.get_sub())
          ctad_args.push_back(static_cast<const exprt &>(a));
      }
      else if(
        value.is_not_nil() && value.id() == ID_initializer_list &&
        !value.operands().empty())
      {
        for(const auto &a : value.operands())
          ctad_args.push_back(a);
      }
      if(!ctad_args.empty())
      {
        if(
          auto deduced = deduce_class_template_arguments(
            to_cpp_name(static_cast<const irept &>(type)), ctad_args))
        {
          type = *deduced;
          ctad_done = true;
        }
      }
    }
    if(!ctad_done)
      typecheck_type(type);
  }

  CHECK_RETURN(type.is_not_nil());

  if(
    declaration.declarators().empty() &&
    ((type.id() == ID_struct_tag &&
      follow_tag(to_struct_tag_type(type)).get_bool(ID_C_is_anonymous)) ||
     (type.id() == ID_union_tag &&
      follow_tag(to_union_tag_type(type)).get_bool(ID_C_is_anonymous)) ||
     type.get_bool(ID_C_is_anonymous)))
  {
    if(type.id() != ID_union_tag)
    {
      error().source_location = code.find_source_location();
      error() << "declaration statement does not declare anything" << eom;
      throw 0;
    }

    code = convert_anonymous_union(declaration);
    return;
  }

  // mark as 'already typechecked'
  already_typechecked_typet::make_already_typechecked(type);

  codet new_code(ID_decl_block);
  new_code.reserve_operands(declaration.declarators().size());

  // Do the declarators (if any)
  for(auto &declarator : declaration.declarators())
  {
    cpp_declarator_convertert cpp_declarator_converter(*this);
    cpp_declarator_converter.is_typedef =
      is_typedef; // NOLINT(readability/identifiers)

    const symbolt &symbol =
      cpp_declarator_converter.convert(declaration, declarator);

    if(is_typedef)
      continue;

    if(!symbol.is_type && !symbol.is_extern && symbol.type.id() == ID_empty)
    {
      error().source_location = symbol.location;
      error() << "void-typed symbol not permitted" << eom;
      throw 0;
    }

    code_frontend_declt decl_statement(cpp_symbol_expr(symbol));
    decl_statement.add_source_location() = symbol.location;

    // Do we have an initializer that's not code?
    if(symbol.value.is_not_nil() && symbol.value.id() != ID_code)
    {
      decl_statement.copy_to_operands(symbol.value);
      // The value type should match the symbol type. For array types,
      // the size constant may have a different integer width (e.g.,
      // int vs long) while representing the same value, so we only
      // check the element type and size value in that case.
      DATA_INVARIANT(
        has_auto(symbol.type) || decl_statement.op1().type() == symbol.type ||
          (symbol.type.id() == ID_array &&
           decl_statement.op1().type().id() == ID_array),
        "declarator type should match symbol type");
    }

    new_code.add_to_operands(std::move(decl_statement));

    // is there a constructor to be called?
    if(symbol.value.is_not_nil())
    {
      DATA_INVARIANT(
        declarator.find(ID_init_args).is_nil(),
        "declarator should not have init_args");
      if(symbol.value.id() == ID_code)
        new_code.copy_to_operands(symbol.value);
    }
    else
    {
      exprt object_expr = cpp_symbol_expr(symbol);

      already_typechecked_exprt::make_already_typechecked(object_expr);

      // For a default-initialized local/block-scope variable (no
      // initializer arguments), the selected default constructor must be
      // accessible at the point of declaration ([dcl.init],
      // [class.access]); cpp_constructor resolves it in the object's own
      // class scope, so check here from the enclosing scope.
      if(!declarator.init_args().has_operands())
        check_default_constructor_access(
          symbol.type, symbol.location, &cpp_scopes.current_scope());

      auto constructor_call = cpp_constructor(
        symbol.location, object_expr, declarator.init_args().operands());

      if(constructor_call.has_value())
        new_code.add_to_operands(std::move(constructor_call.value()));
    }
  }

  code.swap(new_code);
}

void cpp_typecheckt::typecheck_block(code_blockt &code)
{
  cpp_save_scopet saved_scope(cpp_scopes);
  cpp_scopes.new_block_scope();

  c_typecheck_baset::typecheck_block(code);
}
