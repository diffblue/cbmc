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
#include <util/pointer_offset_size.h>
#include <util/symbol_table_base.h>

#include "cpp_convert_type.h"
#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"

#include <optional>

std::optional<exprt> cpp_typecheckt::build_init_list_argument(
  const typet &target_type,
  const exprt &init_list)
{
  if(target_type.id() != ID_struct_tag)
    return {};

  if(!has_viable_init_list_constructor(target_type, init_list))
    return {};

  // Find the initializer_list<U> parameter type of the (non-explicit)
  // initializer-list constructor.
  const struct_typet &struct_type = follow_tag(to_struct_tag_type(target_type));
  irep_idt il_tag_id;
  for(const auto &c : struct_type.components())
  {
    if(c.type().id() != ID_code || c.get_bool(ID_from_base))
      continue;
    const code_typet &code_type = to_code_type(c.type());
    if(code_type.return_type().id() != ID_constructor)
      continue;
    const auto &params = code_type.parameters();
    if(params.size() <= 1)
      continue;
    for(const auto &p : params)
    {
      if(p.get_this())
        continue;
      typet pt = p.type();
      if(is_reference(pt))
        pt = to_pointer_type(pt).base_type();
      if(
        pt.id() == ID_struct_tag &&
        id2string(to_struct_tag_type(pt).get_identifier())
            .find("tag-initializer_list<") != std::string::npos)
      {
        il_tag_id = to_struct_tag_type(pt).get_identifier();
      }
      break;
    }
    if(!il_tag_id.empty())
      break;
  }

  if(il_tag_id.empty())
    return {};

  return build_initializer_list_value(struct_tag_typet{il_tag_id}, init_list);
}

/// Build a `std::initializer_list<E>` value from a braced-init-list, per N5008
/// [dcl.init.list]/5: a backing `const E[N]` array is synthesised from the list
/// elements and the initializer_list object is constructed to refer to it (its
/// modelled `{begin pointer, size}` layout).  \p il_type must be a
/// `std::initializer_list<E>` struct-tag type.
std::optional<exprt> cpp_typecheckt::build_initializer_list_value(
  const struct_tag_typet &il_type,
  const exprt &init_list)
{
  const struct_typet &il_struct = follow_tag(il_type);

  // The std::initializer_list<U> layout is modelled as a {begin pointer,
  // size} pair; extract the element type U from the pointer member.
  typet elem_type;
  const struct_typet::componentt *ptr_comp = nullptr;
  const struct_typet::componentt *size_comp = nullptr;
  for(const auto &m : il_struct.components())
  {
    if(
      m.type().id() == ID_code || m.get_bool(ID_is_type) ||
      m.get_bool(ID_is_static))
      continue;
    if(!ptr_comp)
    {
      ptr_comp = &m;
      if(m.type().id() == ID_pointer)
      {
        elem_type = to_pointer_type(m.type()).base_type();
        elem_type.remove(ID_C_constant);
      }
    }
    else if(!size_comp)
      size_comp = &m;
  }

  if(elem_type.is_nil() || ptr_comp == nullptr || size_comp == nullptr)
    return {};

  try
  {
    exprt::operandst typed_elems;
    for(const auto &op : init_list.operands())
    {
      exprt val = op;
      typecheck_expr(val);
      implicit_typecast(val, elem_type);
      typed_elems.push_back(std::move(val));
    }

    const std::size_t n = typed_elems.size();
    auto arr_type = array_typet{elem_type, from_integer(n, size_type())};
    const std::string arr_id =
      "__init_list_arr$" + std::to_string(anon_counter++);
    auxiliary_symbolt arr_sym;
    arr_sym.name = arr_id;
    arr_sym.base_name = arr_id;
    arr_sym.type = arr_type;
    arr_sym.type.set(ID_C_constant, true);
    arr_sym.mode = ID_cpp;
    arr_sym.is_static_lifetime = true;
    arr_sym.is_lvalue = true;
    arr_sym.location = init_list.source_location();
    arr_sym.value = array_exprt{std::move(typed_elems), arr_type};
    symbol_table.insert(std::move(arr_sym));

    struct_exprt il_val{{}, il_type};
    symbol_exprt arr_ref{arr_id, arr_type};
    arr_ref.set(ID_C_lvalue, true);
    index_exprt first{arr_ref, from_integer(0, c_index_type()), elem_type};
    address_of_exprt addr{first};
    addr.type() = ptr_comp->type();
    il_val.add_to_operands(std::move(addr));
    il_val.add_to_operands(from_integer(n, size_comp->type()));
    il_val.add_source_location() = init_list.source_location();
    return std::move(il_val);
  }
  catch(...)
  {
    // element conversion failed
    return {};
  }
}

/// Initialize an object with a value
void cpp_typecheckt::convert_initializer(symbolt &symbol)
{
  const irep_idt sym_id = symbol.name;
  // this is needed for template arguments that are types

  if(symbol.is_type)
  {
    if(symbol.value.is_nil())
      return;

    if(symbol.value.id() != ID_type)
    {
      error().source_location = symbol.location;
      error() << "expected type as initializer for '" << symbol.base_name << "'"
              << eom;
      throw 0;
    }

    typecheck_type(symbol.value.type());

    return;
  }

  // do we have an initializer?
  if(symbol.value.is_nil())
  {
    // do we need one?
    if(is_reference(symbol.type))
    {
      error().source_location = symbol.location;
      error() << "'" << symbol.base_name
              << "' is declared as reference but is not initialized" << eom;
      throw 0;
    }

    // C++20: lambda in unevaluated context (decltype).
    // The type carries the lambda function address so that
    // default-initialization produces a valid function pointer.
    const irept &lambda_init = symbol.type.find("#lambda_initializer");
    if(lambda_init.is_not_nil())
    {
      symbol.value = static_cast<const exprt &>(lambda_init);
      return;
    }

    // done
    return;
  }

  // we do have an initializer

  // A catch variable ([except.handle]): its value is supplied by the exception
  // object at runtime, so nondet-initialize it here without synthesising a
  // constructor.  This is marked #exception_catch_init by typecheck_try_catch;
  // handling it uniformly (for scalar and class catch variables alike) avoids
  // trying to construct a class-typed catch variable from the int placeholder.
  if(symbol.value.get_bool("#exception_catch_init"))
  {
    side_effect_expr_nondett nondet{symbol.type, symbol.location};
    // Mark the placeholder so the goto-level exception-lowering pass
    // (remove_cpp_exceptions) can rewrite it to read the thrown value.
    nondet.set("#exception_catch_init", true);
    symbol.value = std::move(nondet);
    return;
  }

  // [expr.const]: the initializer of a constexpr (or constinit) variable -- and
  // of a const variable usable in constant expressions -- is manifestly
  // constant-evaluated, so __builtin_is_constant_evaluated() is true within it
  // ([meta.const.eval]/1).  Such variables are flagged is_macro by the
  // declarator converter (constexpr storage); mark the context accordingly
  // while the initializer is type-checked.
  std::optional<constant_expression_contextt> constexpr_init_guard;
  if(symbol.is_macro && !symbol.is_type)
    constexpr_init_guard.emplace(*this);

  // Ensure a class type is fully elaborated before we decide how to
  // initialize it.  In particular cpp_is_pod (used just below to choose
  // between aggregate initialization and constructor invocation) inspects
  // the class's members for user-provided constructors/destructors; a
  // lazily-instantiated class template specialization (e.g.
  // std::__allocated_ptr<A> used inside std::list's _M_create_node) may not
  // yet have those members populated, which would misclassify it as a POD
  // and wrongly route a braced-init-list to member-wise aggregate
  // initialization instead of a constructor call ([dcl.init.list]/3).
  if(symbol.type.id() == ID_struct_tag)
    elaborate_class_template(symbol.type);

  if(is_reference(symbol.type))
  {
    typecheck_expr(symbol.value);

    if(has_auto(symbol.type))
    {
      // C++17: auto x{v} deduces to decltype(v)
      typet deduced_type = symbol.value.type();
      if(
        symbol.value.id() == ID_initializer_list &&
        symbol.value.operands().size() == 1)
      {
        deduced_type = symbol.value.operands().front().type();
        symbol.value = symbol.value.operands().front();
      }
      cpp_convert_auto(symbol.type, deduced_type, get_message_handler());
      // For auto& in const context: if the initializer is const,
      // the reference must also be const (e.g., auto& x = d; in
      // a const method where d is a const member).
      if(
        is_reference(symbol.type) &&
        symbol.value.type().get_bool(ID_C_constant) &&
        symbol.type.id() == ID_pointer)
      {
        to_pointer_type(symbol.type).base_type().set(ID_C_constant, true);
      }
      typecheck_type(symbol.type);
      implicit_typecast(symbol.value, symbol.type);
    }

    reference_initializer(symbol.value, to_reference_type(symbol.type));
  }
  else if(has_auto(symbol.type) && !is_reference(symbol.type))
  {
    // auto type deduction for non-reference types
    // C++11: auto x = {1, 2, 3} deduces std::initializer_list<int>
    if(
      symbol.value.id() == ID_initializer_list &&
      !symbol.value.operands().empty())
    {
      // Type-check the first element to determine T
      exprt first = symbol.value.operands()[0];
      typecheck_expr(first);
      // Build std::initializer_list<T> type
      // For verification purposes, model as a const array
      symbol.type = array_typet(
        first.type(),
        from_integer(symbol.value.operands().size(), size_type()));
      // Type-check all elements
      exprt::operandst elems;
      for(auto &op : symbol.value.operands())
      {
        typecheck_expr(op);
        implicit_typecast(op, first.type());
        elems.push_back(op);
      }
      symbol.value = array_exprt(std::move(elems), to_array_type(symbol.type));
      return;
    }
    typecheck_expr(symbol.value);

    // decltype(auto): if initializer is a function call returning a
    // reference, deduce the reference type
    if(
      symbol.type.id() == ID_decltype && symbol.type.get_bool("#auto") &&
      symbol.value.id() == ID_dereference &&
      is_reference(to_dereference_expr(symbol.value).pointer().type()))
    {
      const typet &ref_type =
        to_dereference_expr(symbol.value).pointer().type();
      cpp_convert_auto(symbol.type, ref_type, get_message_handler());
      typecheck_type(symbol.type);
      reference_initializer(symbol.value, to_reference_type(symbol.type));
      return;
    }

    cpp_convert_auto(symbol.type, symbol.value.type(), get_message_handler());
    typecheck_type(symbol.type);
    implicit_typecast(symbol.value, symbol.type);

    // N5008 [dcl.init]/16.6.2 + [class.copy.elision]: when the deduced
    // type is a non-POD class and the initializer is a materialized
    // temporary (or another class-typed expression), the destination is
    // initialized by the copy/move CONSTRUCTOR chosen by overload
    // resolution -- not by a bitwise assignment.  Leaving the raw
    // temporary here made goto conversion ASSIGN the map bitwise and
    // then run the temporary's DESTRUCTOR: `auto m = std::map<...>{...}`
    // freed the tree nodes m's copied pointers still referenced, and
    // every later at() failed with "deallocated dynamic object".
    // Routing through cpp_constructor selects the move constructor for
    // the rvalue temporary (ownership transfers; the temporary's
    // destructor then frees nothing m uses).
    if(
      symbol.type.id() == ID_struct_tag && !cpp_is_pod(symbol.type) &&
      symbol.value.id() == ID_side_effect &&
      symbol.value.get(ID_statement) == ID_temporary_object)
    {
      symbol_exprt destination(symbol.name, symbol.type);
      destination.set(ID_C_lvalue, true);
      already_typechecked_exprt::make_already_typechecked(destination);
      exprt::operandst ops;
      ops.push_back(symbol.value);
      already_typechecked_exprt::make_already_typechecked(ops.back());
      auto constructor =
        cpp_constructor(symbol.value.source_location(), destination, ops);
      if(constructor.has_value())
        symbol.value = constructor.value();
    }
  }
  else if(cpp_is_pod(symbol.type))
  {
    if(
      symbol.type.id() == ID_pointer &&
      to_pointer_type(symbol.type).base_type().id() == ID_code &&
      symbol.value.id() == ID_address_of &&
      to_address_of_expr(symbol.value).object().id() == ID_cpp_name)
    {
      // initialization of a function pointer with
      // the address of a function: use pointer type information
      // for the sake of overload resolution

      cpp_typecheck_fargst fargs;
      fargs.in_use = true;

      const code_typet &code_type =
        to_code_type(to_pointer_type(symbol.type).base_type());

      for(const auto &parameter : code_type.parameters())
      {
        exprt new_object(ID_new_object, parameter.type());
        new_object.set(ID_C_lvalue, true);

        if(parameter.get_this())
        {
          fargs.has_object = true;
          new_object.type() = to_pointer_type(parameter.type()).base_type();
        }

        fargs.operands.push_back(new_object);
      }

      exprt resolved_expr = resolve(
        to_cpp_name(
          static_cast<irept &>(to_address_of_expr(symbol.value).object())),
        cpp_typecheck_resolvet::wantt::BOTH,
        fargs);

      // For pointer-to-member-function, the symbol type includes a
      // to_member attribute and the resolved expression may have a
      // different representation. Skip the strict type check when
      // pointer-to-member is involved.
      if(
        symbol.type.find(ID_to_member).is_nil() &&
        to_pointer_type(symbol.type).base_type() != resolved_expr.type())
      {
        DATA_INVARIANT_WITH_DIAGNOSTICS(
          false,
          "symbol type must match",
          symbol.type.pretty(),
          resolved_expr.type().pretty(),
          symbol.location);
      }

      if(resolved_expr.id() == ID_symbol)
      {
        symbol.value = address_of_exprt(resolved_expr);

        if(symbol.type.find(ID_to_member).is_not_nil())
          symbol.value.type().add(ID_to_member) =
            symbol.type.find(ID_to_member);
      }
      else if(resolved_expr.id() == ID_member)
      {
        symbol.value = address_of_exprt(
          lookup(resolved_expr.get(ID_component_name)).symbol_expr());

        symbol.value.type().add(ID_to_member) =
          to_member_expr(resolved_expr).compound().type();
      }
      else
        UNREACHABLE;

      if(symbol.type != symbol.value.type())
      {
        error().source_location = symbol.location;
        error() << "conversion from '" << to_string(symbol.value.type())
                << "' to '" << to_string(symbol.type) << "' " << eom;
        throw 0;
      }

      return;
    }

    {
      exprt val = symbol.value;
      try
      {
        typecheck_expr(val);
      }
      catch(...)
      {
        // Type-check of the initializer failed.  This is most often
        // a variable template whose body references an unmodeled
        // libstdc++ helper — for example,
        // `is_trivially_destructible_v<T>`'s body
        // `is_trivially_destructible<T>::value` reaches
        // `__is_destructible_safe<T>` whose
        // `decltype(declval<_Tp&>().~_Tp())` SFINAE chain CBMC's
        // type-checker can't always fully evaluate.
        //
        // Leaving `symbol.value` as the partially-converted cpp_name
        // would corrupt every use of the variable template: the use
        // site in `cpp_typecheck_resolvet::resolve` copies
        // `symbol.value` directly into the resolved expression when
        // `symbol.is_macro` is set (variable templates declared
        // `inline constexpr` are macros in CBMC's representation).
        // A cpp_name with no type then surfaces downstream as
        //   `invalid implicit conversion from '<<type:>>' to 'bool'`.
        //
        // Reset the value to nil so the use site falls back to the
        // `symbol_exprt(name, type)` branch instead of inlining the
        // broken cpp_name.  This is a soft SFINAE-style failure: the
        // symbol still exists with its declared type, but its value
        // is opaque, and downstream uses get a typed symbol_expr.
        symbolt &symbol_w = symbol_table.get_writeable_ref(sym_id);
        symbol_w.value.make_nil();
        throw;
      }
      symbolt &symbol = symbol_table.get_writeable_ref(sym_id);
      symbol.value = std::move(val);
    }

    if(symbol.value.type().find(ID_to_member).is_not_nil())
      symbol.type.add(ID_to_member) = symbol.value.type().find(ID_to_member);

    if(
      symbol.value.id() == ID_initializer_list ||
      symbol.value.id() == ID_string_constant)
    {
      do_initializer(symbol.value, symbol.type, true);

      if(symbol.type.find(ID_size).is_nil())
        symbol.type = symbol.value.type();
    }
    else if(has_auto(symbol.type))
    {
      cpp_convert_auto(symbol.type, symbol.value.type(), get_message_handler());
      typecheck_type(symbol.type);
      implicit_typecast(symbol.value, symbol.type);
    }
    else
      implicit_typecast(symbol.value, symbol.type);

#if 0
    simplify_exprt simplify(*this);
    exprt tmp_value = symbol.value;
    if(!simplify.simplify(tmp_value))
      symbol.value.swap(tmp_value);
#endif
  }
  else
  {
    // we need a constructor
    // Re-acquire symbol reference — earlier type-checking may have
    // invalidated it through symbol table reallocation.
    symbolt &symbol = symbol_table.get_writeable_ref(sym_id);

    // N5008 [dcl.init.list]/5: initializing a std::initializer_list<E> object
    // itself from a braced-init-list is special -- a backing const E[N] array
    // is synthesised and the object refers to it.  This is NOT the general
    // class init-list-constructor path below: initializer_list's own
    // constructors are copy/default/(const E*, size_t) internal, so that path
    // would (wrongly) try to match the elements against them and report
    // "found no match".  Handle it directly.
    if(
      symbol.value.id() == ID_initializer_list &&
      symbol.type.id() == ID_struct_tag &&
      id2string(to_struct_tag_type(symbol.type).get_identifier())
          .find("tag-initializer_list<") != std::string::npos)
    {
      auto il_val = build_initializer_list_value(
        to_struct_tag_type(symbol.type), symbol.value);
      if(il_val.has_value())
      {
        symbol.value = std::move(*il_val);
        return;
      }
    }

    // Aggregate initialization: for braced-init-list on non-POD struct
    // types that have no user-declared constructors (only compiler-
    // generated copy/move constructors), perform member-by-member
    // initialization.  This handles non-POD aggregates such as structs
    // with reference members.
    if(
      symbol.value.id() == ID_initializer_list &&
      symbol.type.id() == ID_struct_tag)
    {
      const struct_typet &struct_type =
        follow_tag(to_struct_tag_type(symbol.type));

      // Find initializer_list<T> constructor AND check for non-copy
      // constructors in ONE pass, before any operation that might
      // invalidate the struct reference through template elaboration.
      bool has_non_copy_ctor = false;
      irep_idt il_tag_id;
      for(const auto &c : struct_type.components())
      {
        if(c.type().id() != ID_code || c.get_bool(ID_from_base))
          continue;
        const code_typet &code_type = to_code_type(c.type());
        if(code_type.return_type().id() != ID_constructor)
          continue;
        const auto &params = code_type.parameters();
        if(params.size() <= 1)
          continue;
        // A copy/move constructor's sole parameter is a reference to the
        // class's own type ([class.copy.ctor]/1).  Such a constructor does
        // not, by itself, make the class a non-aggregate for member-wise
        // initialization.  A two-parameter constructor whose parameter is a
        // reference to some *other* type (e.g. a converting constructor
        // `Wrap(int&)`) is a genuine user-provided constructor and must
        // disable aggregate initialization.
        if(params.size() == 2 && is_reference(params[1].type()))
        {
          const typet &referent = to_pointer_type(params[1].type()).base_type();
          if(
            referent.id() == ID_struct_tag &&
            symbol.type.id() == ID_struct_tag &&
            to_struct_tag_type(referent).get_identifier() ==
              to_struct_tag_type(symbol.type).get_identifier())
            continue;
        }
        has_non_copy_ctor = true;
        // Check first non-this param for initializer_list<T>
        if(il_tag_id.empty())
        {
          for(const auto &p : params)
          {
            if(p.get_this())
              continue;
            typet pt = p.type();
            if(is_reference(pt))
              pt = to_pointer_type(pt).base_type();
            if(
              pt.id() == ID_struct_tag &&
              id2string(to_struct_tag_type(pt).get_identifier())
                  .find("tag-initializer_list<") != std::string::npos)
            {
              il_tag_id = to_struct_tag_type(pt).get_identifier();
            }
            break;
          }
        }
        if(!il_tag_id.empty())
          break;
      }

      // Brace-init-list to std::initializer_list<T> constructor.  Only
      // when this initializer-list constructor is viable for the list
      // ([over.match.list]/1 phase 1.1): otherwise fall through so the
      // elements become the constructor arguments (phase 1.2).  Attempting
      // it when non-viable would emit a spurious element-conversion error
      // (e.g. const char* -> char for `std::string s{p}`).
      if(
        !il_tag_id.empty() &&
        has_viable_init_list_constructor(symbol.type, symbol.value))
      {
        // Re-acquire symbol — the loop may have invalidated it.
        symbolt &symbol = symbol_table.get_writeable_ref(sym_id);
        auto il_val = build_init_list_argument(symbol.type, symbol.value);
        if(il_val.has_value())
        {
          symbol_exprt expr_sym(symbol.name, symbol.type);
          expr_sym.set(ID_C_lvalue, true);
          already_typechecked_exprt::make_already_typechecked(expr_sym);
          exprt::operandst ctor_ops;
          already_typechecked_exprt::make_already_typechecked(*il_val);
          ctor_ops.push_back(std::move(*il_val));
          auto ctor =
            cpp_constructor(symbol.value.source_location(), expr_sym, ctor_ops);
          if(ctor.has_value())
          {
            symbol.value = ctor.value();
            return;
          }
        }
      }

      if(!has_non_copy_ctor)
      {
        const auto &ops = symbol.value.operands();
        std::size_t idx = 0;
        bool aggregate = true;

        // C++17: check if we have base class initializers
        bool has_base_init = struct_type.id() == ID_struct &&
                             !to_struct_type(struct_type).bases().empty();

        if(has_base_init)
        {
          // Convert to constructor-style code that initializes
          // base subobjects and members individually.
          // Copy operands since cpp_constructor may modify symbol.value.
          exprt::operandst ops_copy = symbol.value.operands();
          symbol_exprt sym_expr(symbol.name, symbol.type);
          sym_expr.set(ID_C_lvalue, true);
          already_typechecked_exprt::make_already_typechecked(sym_expr);
          auto init =
            cpp_constructor(symbol.value.source_location(), sym_expr, ops_copy);
          if(init.has_value())
          {
            symbol.value = std::move(*init);
            return;
          }
        }

        struct_exprt result({}, symbol.type);
        for(const auto &c : struct_type.components())
        {
          // [class.bit]/1, [class.mem]: padding inserted for ABI layout is not
          // a member; aggregate initialisation matches initialiser-clauses to
          // members positionally, so a padding component must not consume one.
          if(
            c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
            c.get_bool(ID_is_static) || c.get_is_padding() ||
            c.type().id() == ID_code)
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
          symbol.value = std::move(result);
          return;
        }
      }
    }

    // Complete the bound of an array of unknown bound from its brace-enclosed
    // initializer ([dcl.array]/1, [dcl.init.aggr]/5) before constructing it, so
    // the symbol has a complete type (e.g. for sizeof) and per-element
    // construction below has a definite element count.  (Scalar/POD element
    // types are handled on the POD initializer path above.)
    if(
      symbol.type.id() == ID_array &&
      to_array_type(symbol.type).size().is_nil() &&
      symbol.value.id() == ID_initializer_list)
    {
      to_array_type(symbol.type).size() =
        from_integer(symbol.value.operands().size(), size_type());
    }

    symbol_exprt expr_symbol(symbol.name, symbol.type);
    expr_symbol.set(ID_C_lvalue, true);
    already_typechecked_exprt::make_already_typechecked(expr_symbol);

    exprt::operandst ops;

    // For braced-init-list, first try passing as a single
    // std::initializer_list argument (C++11 [over.match.list]).
    // If that fails, fall back to unpacking the elements as
    // individual constructor arguments.
    if(symbol.value.id() == ID_initializer_list)
    {
      // Per [over.match.list]/1: use an initializer-list constructor with
      // the braced-init-list as a single argument (phase 1.1) only if one
      // is viable; otherwise use the elements of the list as the
      // constructor arguments (phase 1.2).  Attempting a non-viable
      // initializer-list constructor would emit a spurious conversion
      // error (e.g. const char* -> char for `std::string s{p}`).
      if(has_viable_init_list_constructor(symbol.type, symbol.value))
      {
        ops.push_back(symbol.value);
        try
        {
          auto constructor =
            cpp_constructor(symbol.value.source_location(), expr_symbol, ops);
          if(constructor.has_value())
          {
            symbol.value = constructor.value();
            return;
          }
        }
        catch(...)
        {
          // initializer_list constructor not found — fall through
        }
        // Fall back to unpacking
        ops = symbol.value.operands();
      }
      else
        ops = symbol.value.operands();
    }
    else
      ops.push_back(symbol.value);

    auto constructor =
      cpp_constructor(symbol.value.source_location(), expr_symbol, ops);

    if(constructor.has_value())
      symbol.value = constructor.value();
    else
      symbol.value = nil_exprt();
  }
}

void cpp_typecheckt::zero_initializer(
  const exprt &object,
  const typet &type,
  const source_locationt &source_location,
  exprt::operandst &ops)
{
  if(type.id() == ID_struct_tag)
  {
    const auto &struct_type = follow_tag(to_struct_tag_type(type));

    if(struct_type.is_incomplete())
    {
      error().source_location = source_location;
      error() << "cannot zero-initialize incomplete struct" << eom;
      throw 0;
    }

    for(const auto &component : struct_type.components())
    {
      if(component.type().id() == ID_code)
        continue;

      if(component.get_bool(ID_is_type))
        continue;

      if(component.get_bool(ID_is_static))
        continue;

      member_exprt member(object, component.get_name(), component.type());

      // recursive call
      zero_initializer(member, component.type(), source_location, ops);
    }
  }
  else if(
    type.id() == ID_array && !cpp_is_pod(to_array_type(type).element_type()))
  {
    const array_typet &array_type = to_array_type(type);
    const exprt &size_expr = array_type.size();

    if(size_expr.id() == ID_infinity)
      return; // don't initialize

    const mp_integer size =
      numeric_cast_v<mp_integer>(to_constant_expr(size_expr));
    CHECK_RETURN(size >= 0);

    exprt::operandst empty_operands;
    for(mp_integer i = 0; i < size; ++i)
    {
      index_exprt index(
        object, from_integer(i, c_index_type()), array_type.element_type());
      zero_initializer(index, array_type.element_type(), source_location, ops);
    }
  }
  else if(type.id() == ID_union_tag)
  {
    const auto &union_type = follow_tag(to_union_tag_type(type));

    if(union_type.is_incomplete())
    {
      error().source_location = source_location;
      error() << "cannot zero-initialize incomplete union" << eom;
      throw 0;
    }

    // Select the largest component for zero-initialization
    mp_integer max_comp_size = 0;

    union_typet::componentt comp;

    for(const auto &component : union_type.components())
    {
      DATA_INVARIANT(component.type().is_not_nil(), "missing component type");

      if(component.type().id() == ID_code)
        continue;

      auto component_size_opt = size_of_expr(component.type(), *this);

      const auto size_int =
        numeric_cast<mp_integer>(component_size_opt.value_or(nil_exprt()));
      if(size_int.has_value())
      {
        if(*size_int > max_comp_size)
        {
          max_comp_size = *size_int;
          comp = component;
        }
      }
    }

    if(max_comp_size > 0)
    {
      const cpp_namet cpp_name(comp.get_base_name(), source_location);

      exprt member(ID_member);
      member.copy_to_operands(object);
      member.set(ID_component_cpp_name, cpp_name);
      zero_initializer(member, comp.type(), source_location, ops);
    }
  }
  else if(type.id() == ID_c_enum_tag)
  {
    const unsignedbv_typet enum_type(
      to_bitvector_type(follow_tag(to_c_enum_tag_type(type)).underlying_type())
        .get_width());

    exprt zero =
      typecast_exprt::conditional_cast(from_integer(0, enum_type), type);
    already_typechecked_exprt::make_already_typechecked(zero);

    code_frontend_assignt assign;
    assign.lhs() = object;
    assign.rhs() = zero;
    assign.add_source_location() = source_location;

    typecheck_expr(assign.lhs());
    assign.lhs().type().set(ID_C_constant, false);
    already_typechecked_exprt::make_already_typechecked(assign.lhs());

    typecheck_code(assign);
    ops.push_back(assign);
  }
  else
  {
    const auto value = ::zero_initializer(type, source_location, *this);
    if(!value.has_value())
    {
      error().source_location = source_location;
      error() << "cannot zero-initialize '" << to_string(type) << "'" << eom;
      throw 0;
    }

    code_frontend_assignt assign(object, *value);
    assign.add_source_location() = source_location;

    typecheck_expr(assign.lhs());
    assign.lhs().type().set(ID_C_constant, false);
    already_typechecked_exprt::make_already_typechecked(assign.lhs());

    typecheck_code(assign);
    ops.push_back(assign);
  }
}
