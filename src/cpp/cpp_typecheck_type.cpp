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
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/source_location.h>
#include <util/symbol_table_base.h>

#include <ansi-c/c_qualifiers.h>
#include <ansi-c/merged_type.h>

#include "cpp_convert_type.h"
#include "cpp_declaration.h"
#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"

#include <functional>
#include <optional>

/// N5008 [dcl.type.decltype]/1: the type denoted by decltype(E) for an
/// already type-checked expression E.  \p parenthesized records whether E
/// was written as a parenthesized id-expression or member access -- the
/// parser marks those two shapes, which [dcl.type.decltype]/1.3 treats
/// differently from the unparenthesized form (declared type of the entity).
/// Shared by the decltype type-specifier and `decltype(auto)` placeholder
/// deduction ([dcl.type.auto.deduct]/4).
typet cpp_typecheckt::decltype_of(const exprt &e, bool parenthesized)
{
  typet type;

  if(e.type().id() == ID_c_bit_field)
    type = to_c_bit_field_type(e.type()).underlying_type();
  else if(
    !parenthesized && e.id() == ID_address_of && e.get_bool(ID_C_implicit) &&
    to_address_of_expr(e).object().id() == ID_symbol &&
    to_address_of_expr(e).object().type().id() == ID_code)
  {
    // N5008 [dcl.type.decltype]/1.3: `decltype(f)' for a function f is the
    // type of the entity, the function type -- the front end has already
    // applied the function-to-pointer conversion ([conv.func]) to the
    // id-expression, which decltype does not perform.
    type = to_address_of_expr(e).object().type();
  }
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
  else if(
    (e.id() == ID_string_constant ||
     (e.id() == ID_array && e.get_bool(ID_C_string_constant))) &&
    e.type().id() == ID_array)
  {
    // (a wide or UTF string literal is an array constant)
    // N5008 [expr.prim.literal]/1: a string literal is an lvalue, so
    // decltype("abc") is `const char (&)[4]' ([dcl.type.decltype]/1.5);
    // [lex.string]/6: the elements are const
    array_typet array = to_array_type(e.type());
    array.element_type().set(ID_C_constant, true);
    type = ::reference_type(array);
  }
  else if(
    parenthesized && (e.id() == ID_symbol || e.id() == ID_member) &&
    e.get_bool(ID_C_lvalue) && !is_reference(e.type()) &&
    e.type().id() != ID_code)
  {
    // N5008 [dcl.type.decltype]/1.5: `decltype((x))' and `decltype((s.m))'
    // are T& (`const S cs': `decltype((cs.m))' is `const int &').
    type = ::reference_type(e.type());
  }
  else if(e.id() == ID_member)
  {
    // N5008 [dcl.type.decltype]/1.3: an unparenthesized class member
    // access denotes the type of the MEMBER as declared -- `decltype(cs.m)'
    // is `int' for `const S cs', not the access expression's `const int'.
    type = e.type();
    const exprt &compound = to_member_expr(e).compound();
    typet compound_type = compound.type();
    if(
      compound_type.id() == ID_struct_tag || compound_type.id() == ID_union_tag)
    {
      const auto &components =
        follow_tag(to_struct_or_union_tag_type(compound_type)).components();
      const irep_idt &name = to_member_expr(e).get_component_name();
      for(const auto &c : components)
        if(c.get_name() == name)
        {
          type = c.type();
          break;
        }
    }
  }
  else if(e.id() == ID_if && e.get_bool(ID_C_xvalue))
  {
    // N5008 [dcl.type.decltype]/1.4: an xvalue E has decltype T&&; a
    // conditional over two xvalues of one type is an xvalue
    // ([expr.cond]/4.1).
    // (the front end marks an rvalue reference with BOTH flags, see
    // cpp_convert_type.cpp)
    typet rr = ::reference_type(e.type());
    rr.set(ID_C_rvalue_reference, true);
    type = rr;
  }
  else if(
    e.get_bool(ID_C_lvalue) && !is_reference(e.type()) &&
    e.type().id() != ID_code &&
    (e.id() == ID_index || e.id() == ID_comma || e.id() == ID_if ||
     (e.id() == ID_side_effect &&
      (e.get(ID_statement) == ID_assign ||
       e.get(ID_statement) == ID_preincrement ||
       e.get(ID_statement) == ID_predecrement ||
       has_prefix(id2string(e.get(ID_statement)), "assign")))))
  {
    // N5008 [dcl.type.decltype]/1.5: for any other lvalue E, decltype(E)
    // is T&: a subscript, an assignment or compound assignment, a
    // prefix increment, a comma or conditional expression yielding an
    // lvalue.  An unparenthesized id-expression or member access keeps
    // the declared type ([dcl.type.decltype]/1.3); the parenthesized form
    // is handled above.  A compound literal is our representation of the
    // prvalue `T()' / `T{}'.
    type = ::reference_type(e.type());
  }
  else
    type = e.type();

  return cpp_bool_type(type);
}

/// N5008 [expr.rel]/2, [expr.eq]/1, [expr.log.and]/1, [expr.unary.op]/9: a
/// comparison or logical operator yields a prvalue of type bool.  The front
/// end represents it with the internal `__CPROVER_bool' (ID_bool); where the
/// type of an expression becomes a C++ type -- a deduced placeholder, decltype,
/// a deduced template argument -- it is the C++ type bool (ID_c_bool), with
/// the cv-qualifiers kept.
typet cpp_bool_type(const typet &type)
{
  if(type.id() != ID_bool)
    return type;
  typet result = c_bool_type();
  if(type.get_bool(ID_C_constant))
    result.set(ID_C_constant, true);
  if(type.get_bool(ID_C_volatile))
    result.set(ID_C_volatile, true);
  return result;
}

/// N5008 [dcl.type.pack.index]/1-2: replace the pack-index-specifier
/// \p type, `T...[N]' (parsed as an array of T with bound N, marked
/// ID_C_pack_index), by the N-th element of the type parameter pack T, once
/// the pack's elements are known.  The index is a converted constant
/// expression of type size_t that shall be less than the pack size.
/// \return true if the element was selected
bool cpp_typecheckt::select_pack_element(typet &type)
{
  const cpp_namet &name =
    to_cpp_name(static_cast<const irept &>(to_array_type(type).element_type()));
  if(name.is_qualified() || name.has_template_args())
    return false;
  const auto ids = cpp_scopes.current_scope().lookup(
    name.get_base_name(), cpp_scopet::RECURSIVE);
  for(const auto &id_ptr : ids)
  {
    if(id_ptr->id_class != cpp_idt::id_classt::TEMPLATE_PARAMETER)
      continue;
    const auto pack = template_map.pack_args_map.find(id_ptr->identifier);
    if(pack == template_map.pack_args_map.end())
      continue;
    exprt index = to_array_type(type).size();
    {
      constant_expression_contextt constant_expression_guard{*this};
      typecheck_expr(index);
      simplify(index, *this);
    }
    const auto value = numeric_cast<mp_integer>(index);
    if(!value.has_value() || *value < 0 || *value >= pack->second.size())
    {
      error().source_location = type.source_location();
      error() << "pack index out of range" << eom;
      throw 0;
    }
    type = pack->second[numeric_cast_v<std::size_t>(*value)];
    typecheck_type(type);
    return true;
  }
  return false;
}

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
    // GCC type attributes written on this type-name (`uint32_t
    // __attribute__((aligned(8)))' in a typedef/alias, `packed' likewise)
    // sit on the cpp_name node; carry them over to the resolved type as the
    // C front end does for typedef names (c_typecheck_type.cpp).  GCC: "When
    // used as part of a typedef, the aligned attribute can both increase and
    // decrease alignment" -- `typedef S __attribute__((aligned(16))) S16;'
    // gives alignof 16 for a class S as well, but in an ALIAS-DECLARATION
    // g++ ignores the attribute on a class type ("ignoring attributes
    // applied to class type outside of definition": `using A = S
    // __attribute__((aligned(16)))' leaves S's alignment alone).
    const exprt given_alignment =
      static_cast<const exprt &>(type.find(ID_C_alignment));
    const bool given_packed = type.get_bool(ID_C_packed);
    // the `#pragma pack(n)' cap of a member (parse.cpp apply_pragma_pack)
    const exprt given_pragma_pack =
      static_cast<const exprt &>(type.find(ID_C_pragma_pack));

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

    // A template parameter bound to a type deduced from a parsed function
    // type (`function<R(ArgTypes...)>' matched against `int(const int &)':
    // the parameter list is still a cpp_declaration, its element a
    // frontend_pointer) resolves to that unconverted type.  Convert it
    // here, as it would be were it spelled directly: otherwise
    // `static_cast<T &&>(t)' in forward<const int &> saw `frontend_pointer
    // &&', no reference collapsing ([dcl.ref]/6) happened and the body was
    // dropped ("type mismatch on static_cast").
    if(type.id() == ID_frontend_pointer || type.id() == ID_merged_type)
      typecheck_type(type);

    // Phase 2 audit per N5008 [temp.inst]/3.1: when a lazy typedef
    // symbol's alias type just propagated through here, drive
    // on-demand resolution.  The type itself carries the lazy
    // markers and class-scope identifier, so the type-only helper
    // can resolve it without needing back-pointers to the symbol.
    // The helper guards against re-entry into a class still being
    // typechecked.
    if(type.get_bool(ID_C_lazy_member_type))
      try_resolve_lazy_type(type);

    // N5008 [dcl.type.cv]/1, [temp.alias]/2: a type-name denoting a
    // cv-qualified type (an alias template specialization
    // `ident<volatile T>', a typedef of `volatile int', a template
    // parameter bound to one) keeps its qualifiers, joined with any
    // written on the name.  Only `const' was kept, so `volatile' vanished
    // and libc++'s `__enable_if_tuple_size_imp<volatile _Tp, ...>'
    // specializations never matched.
    if(type.get_bool(ID_C_constant))
      qualifiers.is_constant = true;
    if(type.get_bool(ID_C_volatile))
      qualifiers.is_volatile = true;

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

    // N5008 [basic.type.qualifier]/3 and Note 2: cv-qualifiers applied to an
    // array type attach to its element type.  `const T' with T = char[3]
    // (or a typedef of char[3]) is the array of const char, the same type
    // as `const char[3]'; qualify the elements, not only the array.
    for(typet *element = &type; element->id() == ID_array;)
    {
      element = &to_array_type(*element).element_type();
      if(qualifiers.is_constant)
        element->set(ID_C_constant, true);
      if(qualifiers.is_volatile)
        element->set(ID_C_volatile, true);
    }

    const bool class_type = type.id() == ID_struct_tag ||
                            type.id() == ID_union_tag ||
                            type.id() == ID_struct || type.id() == ID_union;
    if(!class_type || !in_alias_declaration)
    {
      if(given_alignment.is_not_nil())
      {
        // N5008 [dcl.align]/5: the alignment-specifier cannot make the
        // alignment weaker than what the type otherwise requires -- here
        // the alignment a typedef-name carries (`typedef short
        // __attribute__((aligned(8))) T; alignas(2) T m;' keeps 8, as g++
        // does).  Keep the stronger of the two.
        const exprt &typedef_alignment =
          static_cast<const exprt &>(type.find(ID_C_alignment));
        const auto given = numeric_cast<mp_integer>(given_alignment);
        const auto existing = typedef_alignment.is_nil()
                                ? std::optional<mp_integer>{}
                                : numeric_cast<mp_integer>(typedef_alignment);
        if(
          given_packed ||
          !(given.has_value() && existing.has_value() && *existing > *given))
        {
          // replacing a typedef's (exact) alignment: the result is exact
          // too (`typedef U __attribute__((aligned(1))) T; T m
          // __attribute__((aligned(8)))' with a 16-byte-aligned U gives 8)
          const bool exact =
            !given_packed && typedef_alignment.get_bool(ID_C_typedef_alignment);
          type.add(ID_C_alignment) = given_alignment;
          if(exact)
          {
            static_cast<exprt &>(type.add(ID_C_alignment))
              .set(ID_C_typedef_alignment, true);
            type.add(ID_C_member_alignment) = given_alignment;
          }
        }
        else
        {
          // kept for a packed struct, where the type's alignment is
          // ignored (padding.cpp explicit_member_alignment)
          type.add(ID_C_member_alignment) = given_alignment;
        }
      }
      if(given_packed)
        type.set(ID_C_packed, true);
    }
    if(given_pragma_pack.is_not_nil())
      type.add(ID_C_pragma_pack) = given_pragma_pack;
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

    // N5008 [dcl.align]/1 + GCC: an alignment specifier in the declaration
    // specifiers (`alignas(16) void *p;', `__attribute__((aligned(16)))
    // void *p;') appertains to the declared OBJECT -- the pointer -- not to
    // the pointed-to type.  The parser merges it into the base type; hoist
    // it, as the C front end does (c_typecheck_type.cpp) -- unless it is
    // the base type's own alignment (a typedef's, or that of a type defined
    // in place).  Likewise the #pragma pack(n) cap of the member.  A
    // reference member is stored as a pointer and g++ aligns it the same
    // way.
    {
      typet &base_type = to_pointer_type(type).base_type();
      const exprt &base_alignment =
        static_cast<const exprt &>(base_type.find(ID_C_alignment));
      if(
        base_alignment.is_not_nil() &&
        !base_alignment.get_bool(ID_C_typedef_alignment) &&
        !base_alignment.get_bool(ID_C_type_alignment) &&
        type.find(ID_C_alignment).is_nil())
      {
        type.add(ID_C_alignment) = base_alignment;
        base_type.remove(ID_C_alignment);
      }
      const irept &base_pragma_pack = base_type.find(ID_C_pragma_pack);
      if(base_pragma_pack.is_not_nil() && type.find(ID_C_pragma_pack).is_nil())
      {
        type.add(ID_C_pragma_pack) = base_pragma_pack;
        base_type.remove(ID_C_pragma_pack);
      }
    }

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
          class_object.get_sub().back().id() == ID_scope_resolution,
          "scope suffix expected");
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
  else if(
    type.id() == ID_array && type.get_bool(ID_C_pack_index) &&
    to_array_type(type).element_type().id() == ID_cpp_name &&
    to_array_type(type).size().is_not_nil() && select_pack_element(type))
  {
    // N5008 [dcl.type.pack.index]/1: `T...[N]' denotes the N-th element of
    // the pack T (select_pack_element replaced it)
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

      // Give a constant bound the index type, as the C front-end
      // (typecheck_array_type) and string literals (string_constantt) do.
      // Array types are compared structurally, so `const char[4]' spelled
      // as a declarator (bound typed `int') was a different type from
      // `decltype("abc")' or `T4' for `typedef const char T4[4];' (bound
      // typed `long'): `is_same<remove_reference_t<decltype("abc")>,
      // const char[4]>' was false.  A dependent bound is left alone so it
      // still matches a `T (&)[N]' pattern.
      if(size_expr.is_constant())
      {
        make_index_type(size_expr);
        simplify(size_expr, *this);
      }
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

    // N5008 [basic.scope.param]/1: a parameter's scope begins at its
    // declaration and includes the rest of the parameter-declaration-clause,
    // so a later parameter's type may name an earlier parameter in an
    // unevaluated operand -- `__rewrap(_Iter __orig_iter,
    // decltype(std::__unwrap_iter(__orig_iter)) __iter)' (libc++).  The
    // parameter symbols proper are created when the definition is
    // converted; here, when a parameter type contains a decltype, the
    // earlier parameters are bound as local symbols of a block scope
    // ([basic.scope.param] note 1: usable for their type only).
    std::optional<cpp_save_scopet> parameter_scope;
    const auto contains_decltype = [](const typet &t)
    {
      std::function<bool(const irept &)> walk = [&](const irept &n)
      {
        if(n.id() == ID_decltype)
          return true;
        for(const auto &sub : n.get_sub())
          if(walk(sub))
            return true;
        for(const auto &ns : n.get_named_sub())
          if(walk(ns.second))
            return true;
        return false;
      };
      return walk(t);
    };
    for(std::size_t i = 0; i < parameters.size(); ++i)
    {
      auto &param = parameters[i];
      if(i > 0 && contains_decltype(param.type()))
      {
        if(!parameter_scope.has_value())
        {
          parameter_scope.emplace(cpp_scopes);
          cpp_scopes.new_block_scope();
        }
        for(std::size_t j = 0; j < i; ++j)
        {
          const irep_idt &name = parameters[j].get_base_name();
          if(
            !name.empty() && parameters[j].type().is_not_nil() &&
            parameters[j].type().id() != ID_cpp_name &&
            cpp_scopes.current_scope()
              .lookup(name, cpp_scopet::SCOPE_ONLY)
              .empty())
          {
            bind_requires_parameter(name, parameters[j].type());
          }
        }
      }
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
        if(
          compound_body_depth > 0 &&
          param.default_value().id() != ID_cpp_deferred_default_argument)
        {
          // N5008 [class.mem.general]/7-8: a default argument within the
          // member-specification is a complete-class context -- it is
          // looked up and checked as if the class were complete, so
          // `path &replace_extension(const path &r = path())' may name
          // the class's own (not yet declared) default constructor, and
          // `void f(int n = _S_max)' a static member declared further
          // down.  Checking it here, while the class is still being
          // defined, failed and abandoned the rest of the class body
          // (every later member unknown).  Keep the parsed expression
          // together with the declaring scope; it is checked on first
          // use at a call site (typecheck_function_call_arguments), by
          // which time the class is complete.
          exprt deferred{ID_cpp_deferred_default_argument, param.type()};
          deferred.add_source_location() =
            param.default_value().source_location();
          deferred.set(ID_C_identifier, cpp_scopes.current_scope().identifier);
          deferred.add_to_operands(std::move(param.default_value()));
          param.default_value() = std::move(deferred);
        }
        else if(param.default_value().id() != ID_cpp_deferred_default_argument)
        {
          typecheck_expr(param.default_value());
          implicit_typecast(param.default_value(), param.type());
        }
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
      else if(
        tmp_type.id() == ID_array &&
        to_array_type(tmp_type).element_type().id() == ID_cpp_name)
      {
        // GCC's typeof (gcc.gnu.org/onlinedocs/gcc/Typeof.html) takes an
        // expression or a type-id; `__typeof__(a[0])' parses as the type-id
        // "array of 0 a".  As for sizeof ([dcl.ambig.res]/2 resolves such
        // an operand of sizeof by what the name denotes), when `a' does not
        // name a type it is the expression a[0].
        cpp_typecheck_fargst fargs;
        exprt symbol_expr = resolve(
          to_cpp_name(
            static_cast<const irept &>(to_array_type(tmp_type).element_type())),
          cpp_typecheck_resolvet::wantt::BOTH,
          fargs);
        if(symbol_expr.id() != ID_type)
        {
          exprt index{ID_index};
          index.add_to_operands(
            std::move(symbol_expr), exprt{to_array_type(tmp_type).size()});
          index.add_source_location() = type.source_location();
          typecheck_expr(index);
          type = index.type();
        }
        else
        {
          typecheck_type(tmp_type);
          type = tmp_type;
        }
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

    exprt e = static_cast<const exprt &>(type.find(ID_expr_arg));

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
    // The pack is the one of the template whose declaration is being
    // checked (the current template scope); a function template
    // declaration seeds an empty-pack entry for its own pack
    // (typecheck_function_template), so entries of other templates may be
    // present too and must not block the reduction.
    std::optional<std::size_t> scope_pack_n;
    {
      const std::string prefix = id2string(cpp_scopes.current_scope().prefix);
      std::size_t matches = 0;
      for(const auto &ps : template_map.pack_size_map)
      {
        const std::string id = id2string(ps.first);
        if(
          !prefix.empty() && id.compare(0, prefix.size(), prefix) == 0 &&
          id.find("::", prefix.size()) == std::string::npos)
        {
          ++matches;
          scope_pack_n = ps.second;
        }
      }
      if(matches != 1)
        scope_pack_n.reset();
      if(!scope_pack_n.has_value() && template_map.pack_size_map.size() == 1)
        scope_pack_n = template_map.pack_size_map.begin()->second;
    }
    if(scope_pack_n.has_value())
    {
      const std::size_t pack_n = *scope_pack_n;
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
          // discarded with the decltype expression.  They are lvalues,
          // like the named parameters they stand for.
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
            // the function parameter pack: a simple name in the pattern
            // that names nothing in scope -- the parameters are not
            // declared while the trailing-return-type is checked, whereas
            // a callee (`g' in `(g(a) + ...)') is found
            if(
              n.id() == ID_cpp_name && n.get_sub().size() == 1 &&
              n.get_sub().front().id() == ID_name &&
              cpp_scopes.current_scope()
                .lookup(
                  n.get_sub().front().get(ID_identifier), cpp_scopet::RECURSIVE)
                .empty())
            {
              base = n.get_sub().front().get(ID_identifier);
            }
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
              // N5008 [expr.prim.id.unqual]/3: a named function parameter
              // is an lvalue of its (referenced) type, also when declared
              // as a forwarding or rvalue reference
              if(is_reference(elem_t) || is_rvalue_reference(elem_t))
                elem_t = to_reference_type(elem_t).base_type();
              symbol_exprt lvalue_placeholder{irep_idt{}, elem_t};
              lvalue_placeholder.set(ID_C_lvalue, true);
              exprt placeholder = lvalue_placeholder;
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

    // N5008 [temp.variadic]/5: a call-argument pack expansion over a pack
    // of the enclosing class template (`-> decltype(g(I...))' in a member
    // of `template <unsigned long... I> struct S'): the member's type is
    // checked here directly, with only the pack's first element bound to
    // its name, so expand the template packs (not function parameter
    // packs, expanded with the parameters) first
    template_map.expand_call_argument_packs(e, /*only_nontype=*/true);

    // recorded by the parser on a parenthesized id-expression / member
    // access; the type check may rebuild the node, so read it first
    const bool parenthesized = e.get_bool(ID_C_parenthesized);

    {
      // [dcl.type.decltype]/1, [expr.context]/1: the operand is unevaluated
      unevaluated_operandt unevaluated_guard{*this};
      typecheck_expr(e);
    }

    type = decltype_of(e, parenthesized);

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

    // N5008 [meta.trans.other]/3: remove_cvref_t<T> is
    // remove_cv_t<remove_reference_t<T>> -- the reference goes first, the
    // cv-qualifiers are those of the referenced type (`const int &' -> int)
    if(type.id() == ID_remove_cvref)
    {
      if(
        tmp_type.id() == ID_pointer &&
        (tmp_type.get_bool(ID_C_reference) ||
         tmp_type.get_bool(ID_C_rvalue_reference)))
      {
        tmp_type = to_pointer_type(tmp_type).base_type();
      }
    }

    if(type.id() == ID_remove_cv || type.id() == ID_remove_cvref)
    {
      tmp_type.remove(ID_C_constant);
      tmp_type.remove(ID_C_volatile);
    }

    // N5008 [meta.trans.other] decay<T>: with U = remove_reference_t<T>, an
    // array of U is a pointer to its element type, a function type a pointer
    // to it, any other type remove_cv_t<U> (GCC's and Clang's __decay)
    if(type.id() == ID_remove_cvref && type.get_bool(ID_C_decay))
    {
      if(tmp_type.id() == ID_array)
        tmp_type = pointer_type(to_array_type(tmp_type).element_type());
      else if(tmp_type.id() == ID_code)
      {
        convert_parsed_parameters(to_code_type(tmp_type));
        tmp_type = pointer_type(tmp_type);
      }
    }

    // N5008 [meta.trans.cv]/2-3: remove_const removes only the
    // top-level const, remove_volatile only the top-level volatile
    // (clang's __remove_const/__remove_volatile builtins, used by
    // libc++'s __remove_const_t in <__atomic/cxx_atomic_impl.h>).
    if(type.id() == ID_remove_const)
      tmp_type.remove(ID_C_constant);
    if(type.id() == ID_remove_volatile)
      tmp_type.remove(ID_C_volatile);

    if(type.id() == ID_remove_reference)
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
        // [tab:meta.trans.sign]: a signed (unsigned) integer type is kept,
        // an unsigned (signed) one becomes its corresponding type
        // ([basic.fundamental]/2-3: same rank); otherwise -- plain char,
        // wchar_t, char8_t ... -- the type of the smallest rank with the
        // same size.  Return the C types with their #c_type, so that a
        // template-id naming the result (`type_identity<__make_signed(S)>')
        // is the same specialization as one spelled with the type itself.
        const std::size_t width = to_bitvector_type(stripped).get_width();
        const irep_idt &c_type = stripped.get(ID_C_c_type);
        const bool keep =
          make_uns ? stripped.id() == ID_unsignedbv && c_type != ID_char &&
                       c_type != ID_wchar_t && c_type != ID_char16_t &&
                       c_type != ID_char32_t && c_type != "char8_t"
                   : stripped.id() == ID_signedbv && c_type != ID_char &&
                       c_type != ID_wchar_t;
        if(keep)
          result = stripped;
        else if(c_type == ID_signed_char || c_type == ID_unsigned_char)
          result =
            make_uns ? typet{unsigned_char_type()} : typet{signed_char_type()};
        else if(
          c_type == ID_signed_short_int || c_type == ID_unsigned_short_int)
          result = make_uns ? typet{unsigned_short_int_type()}
                            : typet{signed_short_int_type()};
        else if(c_type == ID_signed_int || c_type == ID_unsigned_int)
          result =
            make_uns ? typet{unsigned_int_type()} : typet{signed_int_type()};
        else if(c_type == ID_signed_long_int || c_type == ID_unsigned_long_int)
          result = make_uns ? typet{unsigned_long_int_type()}
                            : typet{signed_long_int_type()};
        else if(
          c_type == ID_signed_long_long_int ||
          c_type == ID_unsigned_long_long_int)
          result = make_uns ? typet{unsigned_long_long_int_type()}
                            : typet{signed_long_long_int_type()};
        else
        {
          // the smallest rank with the same width
          std::vector<typet> candidates;
          if(make_uns)
          {
            candidates = {
              unsigned_char_type(),
              unsigned_short_int_type(),
              unsigned_int_type(),
              unsigned_long_int_type(),
              unsigned_long_long_int_type()};
          }
          else
          {
            candidates = {
              signed_char_type(),
              signed_short_int_type(),
              signed_int_type(),
              signed_long_int_type(),
              signed_long_long_int_type()};
          }
          for(const auto &candidate : candidates)
          {
            if(to_bitvector_type(candidate).get_width() == width)
            {
              result = candidate;
              break;
            }
          }
          if(result.is_nil())
          {
            if(make_uns)
              result = unsignedbv_typet{width};
            else
              result = signedbv_typet{width};
          }
        }
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

/// N5008 [dcl.typedef]/2: an alias-declaration `using F = void(int);' has
/// the same semantics as `typedef void F(int);'.  The type-id's function
/// type comes from the parser with its parameters still in parsed form
/// (cpp_declaration), which typecheck_type keeps (the partial-specialization
/// matcher compares that form); the typedef form's declarator is converted to
/// `parameter's, and its noexcept to #C_noexcept.  Convert them, so that F is
/// the type of a function declared `void cb(int)' (`F *p = &cb;').
void cpp_typecheckt::convert_parsed_parameters(code_typet &code_type)
{
  code_typet::parameterst converted;
  for(const auto &parameter : code_type.parameters())
  {
    if(parameter.id() != ID_cpp_declaration)
    {
      converted.push_back(parameter);
      continue;
    }
    const cpp_declarationt &declaration = static_cast<const cpp_declarationt &>(
      static_cast<const exprt &>(parameter));
    if(declaration.declarators().size() != 1)
      return;
    const cpp_declaratort &declarator = declaration.declarators().front();
    // a pack expansion `Ts...' is expanded by substitution, from this form
    if(declarator.get_has_ellipsis())
      return;
    typet type = declarator.merge_type(declaration.type());
    try
    {
      typecheck_type(type);
    }
    catch(...)
    {
      return;
    }
    if(
      type.id() == ID_cpp_name ||
      type.id() == ID_template_parameter_symbol_type)
      return; // dependent
    // [dcl.fct]/5: parameters of array or function type are adjusted
    if(type.id() == ID_array)
      type = pointer_type(to_array_type(type).element_type());
    else if(type.id() == ID_code)
      type = pointer_type(type);
    // [dcl.fct]/5: top-level cv-qualifiers are dropped from the function type
    if(type.id() != ID_pointer || !is_reference(type))
    {
      type.remove(ID_C_constant);
      type.remove(ID_C_volatile);
    }
    code_typet::parametert new_parameter{type};
    const cpp_namet &name = declarator.name();
    if(name.is_not_nil() && name.is_simple_name())
    {
      new_parameter.set_identifier(name.get_base_name());
      new_parameter.set_base_name(name.get_base_name());
    }
    if(declarator.value().is_not_nil())
      new_parameter.default_value() = declarator.value();
    converted.push_back(std::move(new_parameter));
  }
  // `void(void)'
  if(converted.size() == 1 && converted.front().type().id() == ID_empty)
    converted.clear();
  code_type.parameters() = std::move(converted);
  // the declarator form records noexcept as #C_noexcept (rDeclarator)
  if(code_type.get_bool(ID_noexcept))
  {
    code_type.remove(ID_noexcept);
    code_type.set("#C_noexcept", true);
  }
}
