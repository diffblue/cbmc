/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/source_location.h>
#include <util/std_code.h>
#include <util/std_types.h>
#include <util/string_constant.h>
#include <util/symbol_table_base.h>

#include "cpp_declarator_converter.h"
#include "cpp_exception_id.h"
#include "cpp_sfinae_context.h"
#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"
#include "cpp_util.h"

void cpp_typecheckt::typecheck_return(code_frontend_returnt &code)
{
  // Lambda return type deduction: when return_type is auto, just typecheck
  // the return expression without implicit conversion, then set return_type.
  if(return_type.id() == ID_auto)
  {
    if(code.has_return_value())
    {
      typecheck_expr(code.return_value());
      return_type = code.return_value().type();
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
  if(
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

  c_typecheck_baset::typecheck_return(code);

  // For non-POD class-type return values, insert a copy constructor call.
  if(
    code.has_return_value() && !is_reference(return_type) &&
    !cpp_is_pod(return_type) &&
    (return_type.id() == ID_struct_tag || return_type.id() == ID_union_tag) &&
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
      // Skip types from the std namespace to avoid crashes from
      // incomplete destructor chains in STL types.
      const irep_idt &tag_id = to_struct_tag_type(return_type).get_identifier();
      if(id2string(tag_id).find("std::") != std::string::npos)
        return;

      exprt temporary;
      new_temporary(
        code.return_value().source_location(),
        return_type,
        already_typechecked_exprt{code.return_value()},
        temporary);
      code.return_value().swap(temporary);
    }
  }
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

      // Materialize into a temporary array variable
      const std::string scope_prefix =
        id2string(cpp_scopes.current_scope().prefix);
      const std::string arr_id = scope_prefix + "__range_arr";
      {
        auxiliary_symbolt sym;
        sym.name = arr_id;
        sym.base_name = "__range_arr";
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

    // Resolve auto type
    typet var_type = cpp_decl.type();
    if(var_type.id() == ID_auto)
      var_type = elem_type;
    else
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
    typecheck_code(body);

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

          // Give the catch variable a nondet initializer to prevent
          // the type-checker from trying to call a constructor.
          // The actual value comes from the exception at runtime.
          if(declarator.value().is_nil())
          {
            exprt zero = from_integer(0, signed_int_type());
            already_typechecked_exprt::make_already_typechecked(zero);
            declarator.value() = std::move(zero);
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
    typecheck_code(to_code(code.cond()));
  }
  else if(code.get_bool(ID_constexpr))
  {
    // C++17 if constexpr: evaluate condition at compile time and
    // discard the branch not taken so that ill-formed code in the
    // discarded branch does not cause errors.
    typecheck_expr(code.cond());
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

void cpp_typecheckt::typecheck_member_initializer(codet &code)
{
  const cpp_namet &member = to_cpp_name(code.find(ID_member));

  // Let's first typecheck the operands.
  Forall_operands(it, code)
  {
    const bool has_array_ini = it->get_bool(ID_C_array_ini);
    typecheck_expr(*it);
    if(has_array_ini)
      it->set(ID_C_array_ini, true);
  }

  // The initializer may be a data member (non-type)
  // or a parent class (type).
  // We ask for VAR only, as we get the parent classes via their
  // constructor!
  cpp_typecheck_fargst fargs;
  fargs.in_use = true;
  fargs.operands = code.operands();

  // We should only really resolve in qualified mode,
  // no need to look into the parent.
  // Plus, this should happen in class scope, not the scope of
  // the constructor because of the constructor arguments.
  exprt symbol_expr =
    resolve(member, cpp_typecheck_resolvet::wantt::VAR, fargs);

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
      exprt dereference(
        ID_dereference,
        to_pointer_type(cpp_scopes.current_scope().this_expr.type())
          .base_type());
      dereference.copy_to_operands(cpp_scopes.current_scope().this_expr);
      cpp_typecheck_fargst deref_fargs;
      deref_fargs.add_object(dereference);

      {
        cpp_save_scopet cpp_saved_scope(cpp_scopes);
        cpp_scopes.go_to(
          *(cpp_scopes.id_map[cpp_scopes.current_scope().class_identifier]));
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

        auto call =
          cpp_constructor(code.source_location(), symbol_expr, wrapped_ops);

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
      const irept *args_source = nullptr;
      if(init_args.get_sub().size() > 0)
        args_source = &init_args;
      else if(
        value.is_not_nil() && value.id() == ID_initializer_list &&
        !value.operands().empty())
      {
        args_source = &value;
      }
      if(args_source != nullptr)
      {
        // Check if the name resolves to a class template without
        // explicit template arguments (CTAD candidate).
        const cpp_namet &cpp_name =
          to_cpp_name(static_cast<const irept &>(type));
        bool has_tmpl_args = false;
        for(const auto &sub : cpp_name.get_sub())
        {
          if(sub.id() == ID_template_args)
          {
            has_tmpl_args = true;
            break;
          }
        }
        bool is_template = false;
        if(!has_tmpl_args)
        {
          const auto id_set = cpp_scopes.current_scope().lookup(
            cpp_name.get_base_name(), cpp_scopet::RECURSIVE);
          for(const auto *id : id_set)
          {
            if(id->id_class == cpp_idt::id_classt::TEMPLATE)
            {
              is_template = true;
              break;
            }
          }
        }
        if(is_template)
        {
          // Determine the number of template type parameters
          std::size_t n_type_params = 0;
          {
            const auto id_set2 = cpp_scopes.current_scope().lookup(
              cpp_name.get_base_name(), cpp_scopet::RECURSIVE);
            for(const auto *id : id_set2)
            {
              if(id->id_class == cpp_idt::id_classt::TEMPLATE)
              {
                const auto &sym = lookup(id->identifier);
                const auto &tmpl_type = static_cast<const template_typet &>(
                  sym.type.find(ID_template_type));
                for(const auto &p : tmpl_type.template_parameters())
                {
                  if(p.id() == ID_type)
                    ++n_type_params;
                }
                break;
              }
            }
          }

          irept template_args(ID_template_args);
          irept &args_sub = template_args.add(ID_arguments);
          std::vector<typet> unique_types;
          for(const auto &a : args_source->get_sub())
          {
            exprt arg = static_cast<const exprt &>(a);
            typecheck_expr(arg);
            bool already_seen = false;
            for(const auto &t : unique_types)
            {
              if(t == arg.type())
              {
                already_seen = true;
                break;
              }
            }
            if(
              !already_seen &&
              (n_type_params == 0 || unique_types.size() < n_type_params))
            {
              unique_types.push_back(arg.type());
            }
          }
          for(const auto &t : unique_types)
          {
            exprt type_arg(ID_type);
            type_arg.type() = t;
            args_sub.get_sub().push_back(type_arg);
          }
          cpp_namet new_name = cpp_name;
          new_name.get_sub().push_back(template_args);
          type = static_cast<typet &>(static_cast<irept &>(new_name));
          typecheck_type(type);
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
