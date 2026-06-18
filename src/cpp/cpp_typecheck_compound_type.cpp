/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <memory>

#ifdef DEBUG
#  include <iostream>
#endif

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_types.h>
#include <util/symbol_table_base.h>

#include <ansi-c/c_qualifiers.h>

#include "cpp_convert_type.h"
#include "cpp_declarator_converter.h"
#include "cpp_name.h"
#include "cpp_sfinae_context.h"
#include "cpp_type2name.h"
#include "cpp_using.h"
#include "cpp_util.h"

#include <algorithm>

bool cpp_typecheckt::has_const(const typet &type)
{
  if(type.id() == ID_const)
    return true;
  else if(type.id() == ID_merged_type)
  {
    for(const typet &subtype : to_type_with_subtypes(type).subtypes())
    {
      if(has_const(subtype))
        return true;
    }

    return false;
  }
  else
    return false;
}

bool cpp_typecheckt::has_volatile(const typet &type)
{
  if(type.id() == ID_volatile)
    return true;
  else if(type.id() == ID_merged_type)
  {
    for(const typet &subtype : to_type_with_subtypes(type).subtypes())
    {
      if(has_volatile(subtype))
        return true;
    }

    return false;
  }
  else
    return false;
}

bool cpp_typecheckt::has_auto(const typet &type)
{
  if(type.id() == ID_auto)
    return true;
  else if(type.id() == ID_decltype && type.get_bool("#auto"))
    return true;
  else if(
    type.id() == ID_merged_type || type.id() == ID_frontend_pointer ||
    type.id() == ID_pointer)
  {
    for(const typet &subtype : to_type_with_subtypes(type).subtypes())
    {
      if(has_auto(subtype))
        return true;
    }

    return false;
  }
  else if(type.id() == ID_code)
  {
    return has_auto(to_code_type(type).return_type());
  }
  else
    return false;
}

cpp_scopet &cpp_typecheckt::tag_scope(
  const irep_idt &base_name,
  bool has_body,
  bool tag_only_declaration)
{
  // The scope of a compound identifier is difficult,
  // and is different from C.
  //
  // For instance:
  // class A { class B {} }   --> A::B
  // class A { class B; }     --> A::B
  // class A { class B *p; }  --> ::B
  // class B { }; class A { class B *p; } --> ::B
  // class B { }; class A { class B; class B *p; } --> A::B

  // If there is a body, or it's a tag-only declaration,
  // it's always in the current scope, even if we already have
  // it in an upwards scope.

  if(has_body || tag_only_declaration)
    return cpp_scopes.current_scope();

  // No body. Not a tag-only-declaration.
  // Check if we have it already. If so, take it.

  // we should only look for tags, but we don't
  const auto id_set =
    cpp_scopes.current_scope().lookup(base_name, cpp_scopet::RECURSIVE);

  for(const auto &id : id_set)
    if(id->is_class())
      return static_cast<cpp_scopet &>(id->get_parent());

  // Tags without body that we don't have already
  // and that are not a tag-only declaration go into
  // the global scope of the namespace.
  return cpp_scopes.get_global_scope();
}

void cpp_typecheckt::typecheck_compound_type(struct_union_typet &type)
{
  // first save qualifiers
  c_qualifierst qualifiers(type);

  // now clear them from the type
  type.remove(ID_C_constant);
  type.remove(ID_C_volatile);
  type.remove(ID_C_restricted);

  // get the tag name
  bool has_tag = type.find(ID_tag).is_not_nil();
  irep_idt base_name;
  cpp_scopet *dest_scope = nullptr;
  bool has_body = type.find(ID_body).is_not_nil();
  bool tag_only_declaration = type.get_bool(ID_C_tag_only_declaration);
  bool is_union = type.id() == ID_union;

  if(!has_tag)
  {
    // most of these should be named by now; see
    // cpp_declarationt::name_anon_struct_union()

    base_name = std::string("#anon_") + std::to_string(++anon_counter);
    type.set(ID_C_is_anonymous, true);
    dest_scope = &cpp_scopes.current_scope();
  }
  else
  {
    const cpp_namet &cpp_name = to_cpp_name(type.find(ID_tag));

    // scope given?
    if(cpp_name.is_simple_name())
    {
      base_name = cpp_name.get_base_name();

      // anonymous structs always go into the current scope
      if(type.get_bool(ID_C_is_anonymous))
        dest_scope = &cpp_scopes.current_scope();
      else
        dest_scope = &tag_scope(base_name, has_body, tag_only_declaration);
    }
    else
    {
      cpp_save_scopet cpp_save_scope(cpp_scopes);
      cpp_typecheck_resolvet cpp_typecheck_resolve(*this);
      cpp_template_args_non_tct t_args;
      dest_scope =
        &cpp_typecheck_resolve.resolve_scope(cpp_name, base_name, t_args);
    }
  }

  // The identifier 'tag-X' matches what the C front-end does!
  // The hyphen is deliberate to avoid collisions with other
  // identifiers.
  const irep_idt symbol_name =
    dest_scope->prefix + "tag-" + id2string(base_name) + dest_scope->suffix;

  // check if we have it already

  if(const auto maybe_symbol = symbol_table.lookup(symbol_name))
  {
    // we do!
    const symbolt &symbol = *maybe_symbol;

    if(has_body)
    {
      if(
        symbol.type.id() == type.id() &&
        to_struct_union_type(symbol.type).is_incomplete())
      {
        // a previously incomplete struct/union becomes complete
        symbolt &writeable_symbol = symbol_table.get_writeable_ref(symbol_name);
        // Preserve template metadata across the type swap — the
        // incomplete type may carry ID_C_template set by
        // class_template_symbol, which the new complete type lacks.
        // Same applies to ID_template_class_instance: the incomplete
        // symbol created for a class-template instance by
        // `cpp_instantiate_template.cpp:372` carries this flag, but
        // the new complete type produced by the parser does not.
        // Without explicit preservation, downstream consumers that
        // gate on `template_class_instance` (e.g. the empty/
        // incomplete-instance retry path inside
        // `elaborate_class_template` and the un-elaborated-scope
        // recovery path in `cpp_typecheck_resolve.cpp`) see the
        // flag as false after the swap and treat partially
        // elaborated instances as fully complete user classes.
        // Concrete observed effect: members of stdlib containers
        // (`std::vector<X>::clear`, `forward_list_as_mapt::swap`,
        // `std::unordered_map<X>::iterator`, ...) accessed inside
        // a sibling template's body fail to resolve because the
        // container instance never gets re-elaborated.
        irept saved_c_template = writeable_symbol.type.find(ID_C_template);
        irept saved_c_template_arguments =
          writeable_symbol.type.find(ID_C_template_arguments);
        const bool saved_template_class_instance =
          writeable_symbol.type.get_bool(ID_template_class_instance);
        writeable_symbol.type.swap(type);
        if(
          writeable_symbol.type.find(ID_C_template).is_nil() &&
          saved_c_template.is_not_nil())
        {
          writeable_symbol.type.set(ID_C_template, saved_c_template);
          writeable_symbol.type.set(
            ID_C_template_arguments, saved_c_template_arguments);
        }
        if(saved_template_class_instance)
          writeable_symbol.type.set(ID_template_class_instance, true);
        typecheck_compound_body(writeable_symbol);

        // An instance completed here (through the incomplete-to-complete
        // swap) rather than through instantiate_template -- e.g. the
        // explicitly/extern-instantiated std::__cxx11::basic_string<char> --
        // never has its deferred inline member bodies drained by
        // instantiate_template, so clean_up() would discard them and members
        // such as _S_copy_chars become no-ops.  Queue them here.  Per N5008
        // [temp.inst]/4 + Note 4 an odr-used (inline) member must be
        // implicitly instantiated, and CBMC links no library that could
        // supply the definition.  Restricted to template instances; only
        // inline (already-bodied) members are queued; idempotent.
        if(
          writeable_symbol.type.get_bool(ID_template_class_instance) &&
          writeable_symbol.type.find(ID_C_template).is_not_nil() &&
          writeable_symbol.type.find(ID_C_template_arguments).is_not_nil())
        {
          queue_deferred_methods_of_instance(writeable_symbol.name);
        }
      }
      else if(symbol.type.get_bool(ID_C_is_anonymous))
      {
        // we silently ignore
      }
      else
      {
        error().source_location = type.source_location();
        error() << "compound tag '" << base_name << "' declared previously\n"
                << "location of previous definition: " << symbol.location
                << eom;
        throw 0;
      }
    }
    else if(symbol.type.id() != type.id())
    {
      error().source_location = type.source_location();
      error() << "redefinition of '" << symbol.pretty_name << "'"
              << " as different kind of tag" << eom;
      throw 0;
    }
  }
  else
  {
    // produce new symbol
    type_symbolt symbol{symbol_name, type, ID_cpp};
    symbol.base_name = base_name;
    symbol.location = type.source_location();
    symbol.module = module;
    symbol.pretty_name = cpp_scopes.current_scope().prefix +
                         id2string(symbol.base_name) +
                         cpp_scopes.current_scope().suffix;
    symbol.type.set(
      ID_tag, cpp_scopes.current_scope().prefix + id2string(symbol.base_name));

    // move early, must be visible before doing body
    symbolt *new_symbol;

    if(symbol_table.move(symbol, new_symbol))
    {
      error().source_location = symbol.location;
      error() << "cpp_typecheckt::typecheck_compound_type: "
              << "symbol_table.move() failed" << eom;
      throw 0;
    }

    // put into dest_scope
    cpp_idt &id = cpp_scopes.put_into_scope(*new_symbol, *dest_scope);

    id.id_class = cpp_idt::id_classt::CLASS;
    id.is_scope = true;
    id.prefix = cpp_scopes.current_scope().prefix +
                id2string(new_symbol->base_name) +
                cpp_scopes.current_scope().suffix + "::";
    id.class_identifier = new_symbol->name;
    id.id_class = cpp_idt::id_classt::CLASS;

    if(has_body)
      typecheck_compound_body(*new_symbol);
    else
    {
      struct_union_typet new_type(new_symbol->type.id());
      new_type.set(ID_tag, new_symbol->base_name);
      new_type.make_incomplete();
      new_type.add_source_location() = type.source_location();
      new_symbol->type.swap(new_type);
    }
  }

  if(is_union)
  {
    // create union tag
    union_tag_typet tag_type(symbol_name);
    qualifiers.write(tag_type);
    type.swap(tag_type);
  }
  else
  {
    // create struct tag
    struct_tag_typet tag_type(symbol_name);
    qualifiers.write(tag_type);
    type.swap(tag_type);
  }
}

void cpp_typecheckt::typecheck_compound_declarator(
  const symbolt &symbol,
  const cpp_declarationt &declaration,
  cpp_declaratort &declarator,
  struct_typet::componentst &components,
  const irep_idt &access,
  bool is_static,
  bool is_typedef,
  bool is_mutable)
{
  bool is_cast_operator = declaration.type().id() == "cpp-cast-operator";

  if(is_cast_operator)
  {
    PRECONDITION(
      declarator.name().get_sub().size() == 2 &&
      declarator.name().get_sub().front().id() == ID_operator);

    typet type = static_cast<typet &>(declarator.name().get_sub()[1]);
    declarator.type().add_subtype() = type;
    typecheck_type(type);

    cpp_namet::namet name("(" + cpp_type2name(type) + ")");
    declarator.name().get_sub().back().swap(name);
  }

  typet final_type = declarator.merge_type(declaration.type());

  {
    bool is_function_member =
      final_type.id() == ID_code || final_type.id() == ID_function_type;
    bool old_suppress = suppress_elaborate;
    if(
      is_function_member &&
      config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::CLANG)
      suppress_elaborate = true;
    try
    {
      typecheck_type(final_type);
    }
    catch(...)
    {
      suppress_elaborate = old_suppress;
      throw;
    }
    suppress_elaborate = old_suppress;

    // A finalised function type must not retain an unconverted
    // `frontend_pointer` parameter.  This can happen for a member of a
    // template class instantiation whose parameter type came from a
    // substituted template parameter pack that was a reference/pointer —
    // e.g. std::function<R(ArgTypes...)>::operator()(ArgTypes...) with a
    // reference parameter.  Convert such parameters to their proper
    // pointer/reference type so overload resolution can form the
    // argument conversion ([over.match]); for ordinary, already-formed
    // parameters this is a no-op.
    if(is_function_member && final_type.id() == ID_code)
    {
      for(auto &param : to_code_type(final_type).parameters())
      {
        if(param.type().id() == ID_frontend_pointer)
        {
          cpp_convert_plain_type(param.type(), get_message_handler());
          typecheck_type(param.type());
        }
      }
    }
  }

  if(final_type.id() == ID_empty && !declaration.is_typedef())
  {
    // During template instantiation, a member's type may resolve to void
    // (e.g., __aligned_membuf<void> in variant). Skip such members
    // instead of erroring — they are intentionally disabled by SFINAE
    // or never used at runtime.
    if(!instantiation_stack.empty())
      return;
    error().source_location = declaration.type().source_location();
    error() << "void-typed member not permitted" << eom;
    throw 0;
  }

  cpp_namet cpp_name;
  cpp_name.swap(declarator.name());

  irep_idt base_name;

  if(cpp_name.is_nil())
  {
    // Yes, there can be members without name.
    base_name = irep_idt();
  }
  else if(cpp_name.is_simple_name())
  {
    base_name = cpp_name.get_base_name();
  }
  else
  {
    error().source_location = cpp_name.source_location();
    error() << "declarator in compound needs to be simple name" << eom;
    throw 0;
  }

  // NOLINTNEXTLINE(readability/identifiers)
  bool is_method = !is_typedef && final_type.id() == ID_code;
  bool is_constructor = declaration.is_constructor();
  bool is_destructor = declaration.is_destructor();
  bool is_virtual = declaration.member_spec().is_virtual();
  bool is_explicit = declaration.member_spec().is_explicit();
  bool is_inline = declaration.member_spec().is_inline();

  final_type.set(ID_C_member_name, symbol.name);

  // first do some sanity checks

  if(is_virtual && !is_method)
  {
    error().source_location = cpp_name.source_location();
    error() << "only methods can be virtual" << eom;
    throw 0;
  }

  if(is_inline && !is_method)
  {
    // C++17 allows inline variables (static inline data members).
    // Just ignore the inline specifier for non-methods.
    is_inline = false;
  }

  if(is_virtual && is_static)
  {
    error().source_location = cpp_name.source_location();
    error() << "static methods cannot be virtual" << eom;
    throw 0;
  }

  if(is_cast_operator && is_static)
  {
    error().source_location = cpp_name.source_location();
    error() << "cast operators cannot be static" << eom;
    throw 0;
  }

  if(is_constructor && is_virtual)
  {
    error().source_location = cpp_name.source_location();
    error() << "constructors cannot be virtual" << eom;
    throw 0;
  }

  if(!is_constructor && !is_cast_operator && is_explicit)
  {
    error().source_location = cpp_name.source_location();
    error() << "only constructors and conversion operators can be explicit"
            << eom;
    throw 0;
  }

  if(is_constructor && base_name != symbol.base_name)
  {
    error().source_location = cpp_name.source_location();
    error() << "member function must return a value or void" << eom;
    throw 0;
  }

  if(is_destructor && base_name != "~" + id2string(symbol.base_name))
  {
    error().source_location = cpp_name.source_location();
    error() << "destructor with wrong name" << eom;
    throw 0;
  }

  // now do actual work

  irep_idt identifier;

  // the below is a temporary hack
  // if(is_method || is_static)
  if(
    id2string(cpp_scopes.current_scope().prefix).find("#anon") ==
      std::string::npos ||
    is_method || is_static)
  {
    // Identifiers for methods include the scope prefix.
    // Identifiers for static members include the scope prefix.
    identifier = cpp_scopes.current_scope().prefix + id2string(base_name);
  }
  else
  {
    // otherwise, we keep them simple
    identifier = base_name;
  }

  struct_typet::componentt component(identifier, final_type);
  component.set(ID_access, access);
  component.set_base_name(base_name);
  component.set_pretty_name(base_name);
  component.add_source_location() = cpp_name.source_location();

  if(cpp_name.is_operator())
  {
    component.set(ID_is_operator, true);
    component.type().set(ID_C_is_operator, true);
  }

  if(is_cast_operator)
    component.set(ID_is_cast_operator, true);

  if(declaration.member_spec().is_explicit())
    component.set(ID_is_explicit, true);

  // either blank, const, volatile, or const volatile
  const typet &method_qualifier =
    static_cast<const typet &>(declarator.add(ID_method_qualifier));

  if(is_static)
  {
    component.set(ID_is_static, true);
    component.type().set(ID_C_is_static, true);
  }

  if(is_typedef)
    component.set(ID_is_type, true);

  if(is_mutable)
    component.set(ID_is_mutable, true);

  exprt &value = declarator.value();
  irept &initializers = declarator.member_initializers();

  if(is_method)
  {
    if(value.id() == ID_code && to_code(value).get_statement() == ID_cpp_delete)
    {
      value.make_nil();
      initializers.make_nil();
      component.set(ID_access, ID_noaccess);
    }

    if(value.id() == ID_code && to_code(value).get_statement() == ID_default)
    {
      if(base_name == "operator<=>")
      {
        // C++20: fix return type from auto to signed int.
        // Body will be generated in do_not_typechecked.
        code_typet &fn_type = to_code_type(component.type());
        fn_type.return_type() = signed_int_type();
      }

      // C++11 [dcl.fct.def.default]: treat = default as having an
      // empty body so that member initialization is generated
      value = codet(ID_block);
      value.add_source_location() = declaration.source_location();
      // Mark this body as coming from an explicitly-defaulted special
      // member.  For a defaulted copy/move constructor, convert_function
      // uses this to generate the memberwise base/member copies lazily (at
      // conversion time, when the class is complete and the ctor is
      // actually being elaborated), per [dcl.fct.def.default] /
      // [class.copy.ctor]/14.
      value.set("#defaulted_function", true);
    }

    component.set(ID_is_inline, declaration.member_spec().is_inline());

    // the 'virtual' name of the function
    std::string virtual_name = id2string(component.get_base_name()) +
                               id2string(function_identifier(component.type()));

    if(has_const(method_qualifier))
      virtual_name += "$const";

    if(has_volatile(method_qualifier))
      virtual_name += "$volatile";

    if(to_code_type(component.type()).return_type().id() == ID_destructor)
      virtual_name = "@dtor";

    // The method may be virtual implicitly.
    std::set<irep_idt> virtual_bases;

    for(const auto &comp : components)
    {
      if(comp.get_bool(ID_is_virtual))
      {
        if(comp.get(ID_virtual_name) == virtual_name)
        {
          is_virtual = true;
          const code_typet &code_type = to_code_type(comp.type());
          DATA_INVARIANT(
            !code_type.parameters().empty(), "must have parameters");
          const typet &pointer_type = code_type.parameters()[0].type();
          DATA_INVARIANT(
            pointer_type.id() == ID_pointer, "this must be pointer");
          virtual_bases.insert(
            to_pointer_type(pointer_type).base_type().get(ID_identifier));
        }
      }
    }

    if(!is_virtual)
    {
      typecheck_member_function(
        symbol, component, initializers, method_qualifier, value);

      // C++11 [dcl.constexpr]: a `constexpr` member function is
      // implicitly inline and may be evaluated at compile time.
      // Mark the symbol with is_macro=true so the constexpr
      // function-call-evaluator in typecheck_side_effect_function_call
      // recognizes it as a candidate for compile-time folding.
      // (`cpp_declarator_converter` does the same for non-member
      // declarations.)
      if(declaration.storage_spec().is_constexpr())
      {
        const irep_idt method_id = component.get_name();
        if(symbolt *m = symbol_table.get_writeable(method_id))
          m->is_macro = true;
      }

      if(!value.is_nil() && !is_static)
      {
        error().source_location = cpp_name.source_location();
        error() << "no initialization allowed here" << eom;
        throw 0;
      }
    }
    else // virtual
    {
      component.type().set(ID_C_is_virtual, true);
      component.type().set(ID_C_virtual_name, virtual_name);

      // Check if it is a pure virtual method
      if(value.is_not_nil() && value.is_constant())
      {
        mp_integer i;
        to_integer(to_constant_expr(value), i);
        if(i != 0)
        {
          error().source_location = declarator.name().source_location();
          error() << "expected 0 to mark pure virtual method, got " << i << eom;
          throw 0;
        }
        component.set(ID_is_pure_virtual, true);
        value.make_nil();
      }

      typecheck_member_function(
        symbol, component, initializers, method_qualifier, value);

      // get the virtual-table symbol type
      irep_idt vt_name = "virtual_table::" + id2string(symbol.name);

      if(!symbol_table.has_symbol(vt_name))
      {
        // first time: create a virtual-table symbol type
        type_symbolt vt_symb_type{vt_name, struct_typet(), ID_cpp};
        vt_symb_type.base_name =
          "virtual_table::" + id2string(symbol.base_name);
        vt_symb_type.pretty_name = vt_symb_type.base_name;
        vt_symb_type.module = module;
        vt_symb_type.location = symbol.location;
        vt_symb_type.type.set(ID_name, vt_symb_type.name);

        const bool failed =
          !symbol_table.insert(std::move(vt_symb_type)).second;
        CHECK_RETURN(!failed);

        // add a virtual-table pointer
        struct_typet::componentt compo(
          id2string(symbol.name) + "::@vtable_pointer",
          pointer_type(struct_tag_typet(vt_name)));
        compo.set_base_name("@vtable_pointer");
        compo.set_pretty_name(id2string(symbol.base_name) + "@vtable_pointer");
        compo.set(ID_is_vtptr, true);
        compo.set(ID_access, ID_public);
        components.push_back(compo);
        put_compound_into_scope(compo);
      }

      typet &vt = symbol_table.get_writeable_ref(vt_name).type;
      INVARIANT(
        vt.id() == ID_struct, "Virtual tables must be stored as struct");
      struct_typet &virtual_table = to_struct_type(vt);

      component.set(ID_virtual_name, virtual_name);
      component.set(ID_is_virtual, is_virtual);

      // add an entry to the virtual table
      struct_typet::componentt vt_entry(
        id2string(vt_name) + "::" + virtual_name,
        pointer_type(component.type()));
      vt_entry.set_base_name(virtual_name);
      vt_entry.set_pretty_name(virtual_name);
      vt_entry.set(ID_access, ID_public);
      vt_entry.add_source_location() = symbol.location;
      virtual_table.components().push_back(vt_entry);

      // take care of overloading
      while(!virtual_bases.empty())
      {
        irep_idt virtual_base = *virtual_bases.begin();

        // a new function that does 'late casting' of the 'this' parameter
        symbolt func_symb{
          id2string(component.get_name()) + "::" + id2string(virtual_base),
          component.type(),
          symbol.mode};
        func_symb.base_name = component.get_base_name();
        func_symb.pretty_name = component.get_base_name();
        func_symb.module = module;
        func_symb.location = component.source_location();

        // change the type of the 'this' pointer
        code_typet &code_type = to_code_type(func_symb.type);
        code_typet::parametert &this_parameter = code_type.parameters().front();
        to_pointer_type(this_parameter.type())
          .base_type()
          .set(ID_identifier, virtual_base);

        // create symbols for the parameters
        code_typet::parameterst &args = code_type.parameters();
        std::size_t i = 0;
        for(auto &arg : args)
        {
          irep_idt param_base_name = arg.get_base_name();

          if(param_base_name.empty())
            param_base_name = "arg" + std::to_string(i++);

          symbolt arg_symb{
            id2string(func_symb.name) + "::" + id2string(param_base_name),
            arg.type(),
            symbol.mode};
          arg_symb.base_name = param_base_name;
          arg_symb.pretty_name = param_base_name;
          arg_symb.location = func_symb.location;

          arg.set_identifier(arg_symb.name);

          // add the parameter to the symbol table
          const bool failed = !symbol_table.insert(std::move(arg_symb)).second;
          CHECK_RETURN(!failed);
        }

        // do the body of the function
        // For multiple inheritance, adjust the 'this' pointer from
        // the base subobject to the derived class.
        const auto &this_param = args[0];
        exprt this_expr = lookup(this_param.get_identifier()).symbol_expr();
        const typet &target_type =
          to_code_type(component.type()).parameters()[0].type();

        // Check if this base class is at a non-zero offset (i.e., not
        // the first/primary base). Only non-primary bases need pointer
        // adjustment.
        const struct_typet &derived_struct =
          to_struct_type(symbol_table.lookup_ref(symbol.name).type);
        bool is_primary_base = false;
        for(const auto &base : derived_struct.bases())
        {
          if(
            base.type().id() == ID_struct_tag &&
            to_struct_tag_type(base.type()).get_identifier() == virtual_base)
          {
            is_primary_base = true;
            break;
          }
          // First base with a vtable is the primary base
          break;
        }

        exprt late_cast;
        if(!is_primary_base)
        {
          // Non-primary base: compute offset and adjust this pointer
          const irep_idt vt_ptr_name =
            id2string(virtual_base) + "::@vtable_pointer";
          auto base_off = member_offset(derived_struct, vt_ptr_name, *this);
          if(base_off.has_value() && *base_off > 0)
          {
            auto char_ptr =
              typecast_exprt(this_expr, pointer_type(unsigned_char_type()));
            auto adjusted = minus_exprt(
              char_ptr, from_integer(*base_off, pointer_diff_type()));
            late_cast = typecast_exprt(adjusted, target_type);
          }
          else
            late_cast = typecast_exprt(this_expr, target_type);
        }
        else
        {
          late_cast = typecast_exprt(this_expr, target_type);
        }

        // Thunk calls must be direct (non-virtual) to avoid infinite
        // recursion through the vtable.
        typet direct_type = component.type();
        direct_type.remove(ID_C_is_virtual);

        side_effect_expr_function_callt expr_call(
          symbol_exprt(component.get_name(), direct_type),
          {late_cast},
          uninitialized_typet{},
          source_locationt{});
        expr_call.arguments().reserve(args.size());

        // Skip the first parameter (this) — it was already added as
        // late_cast above.
        for(std::size_t j = 1; j < args.size(); ++j)
        {
          expr_call.arguments().push_back(
            lookup(args[j].get_identifier()).symbol_expr());
        }

        if(
          code_type.return_type().id() != ID_empty &&
          code_type.return_type().id() != ID_destructor)
        {
          expr_call.type() = to_code_type(component.type()).return_type();

          func_symb.value =
            code_blockt{{code_frontend_returnt(std::move(expr_call))}};
        }
        else
        {
          func_symb.value =
            code_blockt{{code_expressiont(std::move(expr_call))}};
        }

        // add this new function to the list of components

        struct_typet::componentt new_compo = component;
        new_compo.type() = func_symb.type;
        new_compo.set_name(func_symb.name);
        components.push_back(new_compo);

        // add the function to the symbol table
        {
          const bool failed = !symbol_table.insert(std::move(func_symb)).second;
          CHECK_RETURN(!failed);
        }

        put_compound_into_scope(new_compo);

        // next base
        virtual_bases.erase(virtual_bases.begin());
      }
    }
  }

  if(is_static && !is_method) // static non-method member
  {
    // add as global variable to symbol_table
    symbolt static_symbol{identifier, component.type(), symbol.mode};
    static_symbol.base_name = component.get_base_name();
    static_symbol.is_lvalue = true;
    static_symbol.is_static_lifetime = true;
    static_symbol.location = cpp_name.source_location();
    static_symbol.is_extern = true;

    if(declaration.storage_spec().is_constexpr())
    {
      // Don't mark _S_use_relocate/_S_nothrow_relocate as macros.
      // These constexpr functions are overridden with model bodies
      // in provide_stdlib_bodies(). Marking them as macros causes
      // their values to be inlined as nondet during goto conversion,
      // before the model bodies are available.
      const std::string bname = id2string(static_symbol.base_name);
      if(bname != "_S_use_relocate" && bname != "_S_nothrow_relocate")
        static_symbol.is_macro = true;
    }

    // TODO: not sure about this: should be defined separately!
    dynamic_initializations.push_back(static_symbol.name);

    symbolt *new_symbol;
    if(symbol_table.move(static_symbol, new_symbol))
    {
      error().source_location = cpp_name.source_location();
      error() << "redeclaration of static member '" << static_symbol.base_name
              << "'" << eom;
      throw 0;
    }

    // Fold __safe_multiply::__c immediately after creation.
    // __c = uintmax_t(1) << (sizeof(intmax_t) * 4) = 2^32 on 64-bit.
    // Other static members (__a0, __a1, etc.) depend on __c and are
    // evaluated during type-checking, so __c must be available now.
    if(
      id2string(new_symbol->base_name) == "__c" &&
      id2string(new_symbol->name).find("__safe_multiply") != std::string::npos)
    {
      typet t = new_symbol->type;
      t.remove(ID_C_constant);
      new_symbol->value = from_integer(mp_integer(1) << 32, t);
      new_symbol->is_macro = true;
    }

    if(value.is_not_nil())
    {
      // auto type deduction for static constexpr auto members
      if(has_auto(new_symbol->type))
      {
        new_symbol->value.swap(value);
        typecheck_expr(new_symbol->value);

        // C++17: auto x{v} deduces to decltype(v), not
        // initializer_list<decltype(v)>. Unwrap single-element
        // brace-init-lists for auto deduction.
        typet deduced_type = new_symbol->value.type();
        if(
          new_symbol->value.id() == ID_initializer_list &&
          new_symbol->value.operands().size() == 1)
        {
          deduced_type = new_symbol->value.operands().front().type();
          new_symbol->value = new_symbol->value.operands().front();
        }

        cpp_convert_auto(new_symbol->type, deduced_type, get_message_handler());
        typecheck_type(new_symbol->type);
        implicit_typecast(new_symbol->value, new_symbol->type);
        // Update the component type to match
        component.type() = new_symbol->type;
      }
      else if(cpp_is_pod(new_symbol->type))
      {
        new_symbol->value.swap(value);
        {
          // Per [temp.deduct]/8 applied to class-member initializer
          // evaluation during class-template instantiation: treat
          // substitution failure as SFINAE rather than a user-visible
          // error.  Also suppress recursive `elaborate_class_template`
          // to prevent elaboration chains that would re-enter the
          // class currently being elaborated.
          bool old_suppress = suppress_elaborate;
          suppress_elaborate = true;

          try
          {
            sfinae_contextt sfinae_guard{*this};
            // For constexpr/const members during template instantiation,
            // resolve cpp_names in the value expression using the C++
            // type-checker. The C do_initializer can't resolve cpp_name
            // expressions like gcd<Y, X%Y>::value or Abs<N>::value.
            // Temporarily allow elaboration so that referenced templates
            // can be instantiated.
            // Use the C++ type-checker (which resolves cpp_names, evaluates
            // sizeof...(Pack) from pack_size_map per [temp.variadic]/8, etc.)
            // whenever a template substitution is active.  A multi-element
            // parameter pack populates only pack_args_map/pack_size_map (build
            // records a scalar type_map entry only for single-element packs),
            // so checking type_map/expr_map alone misses packs and falls back
            // to the C type-checker, which mis-handles `sizeof...(T)` as
            // `sizeof(T)`.
            bool use_cpp_typecheck = new_symbol->value.is_not_nil() &&
                                     (!template_map.expr_map.empty() ||
                                      !template_map.type_map.empty() ||
                                      !template_map.pack_args_map.empty() ||
                                      !template_map.pack_size_map.empty());
            if(use_cpp_typecheck)
            {
              bool saved_force = force_elaborate;
              force_elaborate = true;
              typecheck_expr(new_symbol->value);
              force_elaborate = saved_force;
              implicit_typecast(new_symbol->value, new_symbol->type);
              simplify(new_symbol->value, *this);
            }
            else
            {
              c_typecheck_baset::do_initializer(*new_symbol);
            }
          }
          catch(...)
          {
            if(new_symbol->is_macro)
            {
              new_symbol->value.visit_pre(
                [this](exprt &e)
                {
                  if(e.id() == ID_symbol)
                  {
                    exprt v =
                      template_map.lookup(to_symbol_expr(e).get_identifier());
                    if(v.is_not_nil())
                      e = v;
                  }
                });
            }
          }

          suppress_elaborate = old_suppress;

          if(
            !new_symbol->is_macro && new_symbol->type.get_bool(ID_C_constant) &&
            (new_symbol->type.id() == ID_signedbv ||
             new_symbol->type.id() == ID_unsignedbv ||
             new_symbol->type.id() == ID_bool ||
             new_symbol->type.id() == ID_c_bool ||
             new_symbol->type.id() == ID_c_enum_tag))
          {
            simplify(new_symbol->value, *this);
            if(new_symbol->value.is_constant())
              new_symbol->is_macro = true;
          }
        }
      }
      else
      {
        symbol_exprt symexpr = symbol_exprt::typeless(new_symbol->name);

        exprt::operandst ops;
        ops.push_back(value);
        auto defcode = cpp_constructor(source_locationt(), symexpr, ops);
        CHECK_RETURN(defcode.has_value());

        new_symbol->value.swap(defcode.value());
      }
    }
  }

  // array members must have fixed size
  check_fixed_size_array(component.type());

  // C++11: store default member initializer on the component
  if(!is_method && !is_static && value.is_not_nil() && value.id() != ID_code)
  {
    component.add(ID_C_default_value, value);
  }

  put_compound_into_scope(component);

  components.push_back(component);
}

/// check that an array has fixed size
void cpp_typecheckt::check_fixed_size_array(typet &type)
{
  if(type.id() == ID_array)
  {
    array_typet &array_type = to_array_type(type);

    if(array_type.size().is_not_nil())
    {
      if(array_type.size().id() == ID_symbol)
      {
        const symbol_exprt &s = to_symbol_expr(array_type.size());
        const symbolt &symbol = lookup(s.identifier());

        if(
          cpp_is_pod(symbol.type) &&
          (symbol.type.get_bool(ID_C_constant) || symbol.is_macro))
          array_type.size() = symbol.value;
      }

      make_constant_index(array_type.size());
    }

    // recursive call for multi-dimensional arrays
    check_fixed_size_array(array_type.element_type());
  }
}

void cpp_typecheckt::put_compound_into_scope(
  const struct_union_typet::componentt &compound)
{
  const irep_idt &base_name = compound.get_base_name();
  const irep_idt &name = compound.get_name();

  // nothing to do if no base_name (e.g., an anonymous bitfield)
  if(base_name.empty())
    return;

  if(compound.type().id() == ID_code)
  {
    // put the symbol into scope
    cpp_idt &id = cpp_scopes.current_scope().insert(base_name);
    id.id_class = compound.get_bool(ID_is_type) ? cpp_idt::id_classt::TYPEDEF
                                                : cpp_idt::id_classt::SYMBOL;
    id.identifier = name;
    id.class_identifier = cpp_scopes.current_scope().identifier;
    id.is_member = true;
    id.is_constructor =
      to_code_type(compound.type()).return_type().id() == ID_constructor;
    id.is_method = true;
    id.is_static_member = compound.get_bool(ID_is_static);

    // create function block-scope in the scope
    cpp_idt &id_block = cpp_scopes.current_scope().insert(
      irep_idt(std::string("$block:") + base_name.c_str()));

    id_block.id_class = cpp_idt::id_classt::BLOCK_SCOPE;
    id_block.identifier = name;
    id_block.class_identifier = cpp_scopes.current_scope().identifier;
    id_block.is_method = true;
    id_block.is_static_member = compound.get_bool(ID_is_static);

    id_block.is_scope = true;
    id_block.prefix = compound.get_string(ID_prefix);
    cpp_scopes.id_map[id.identifier] = &id_block;
  }
  else
  {
    // check if it's already there
    const auto id_set =
      cpp_scopes.current_scope().lookup(base_name, cpp_scopet::SCOPE_ONLY);

    for(const auto &id_it : id_set)
    {
      const cpp_idt &id = *id_it;

      // the name is already in the scope
      // this is ok if they belong to different categories
      if(!id.is_class() && !id.is_enum())
      {
        error().source_location = compound.source_location();
        error() << "'" << base_name << "' already in compound scope" << eom;
        throw 0;
      }
    }

    // put into the scope
    cpp_idt &id = cpp_scopes.current_scope().insert(base_name);
    id.id_class = compound.get_bool(ID_is_type) ? cpp_idt::id_classt::TYPEDEF
                                                : cpp_idt::id_classt::SYMBOL;
    id.identifier = name;
    id.class_identifier = cpp_scopes.current_scope().identifier;
    id.is_member = true;
    id.is_method = false;
    id.is_static_member = compound.get_bool(ID_is_static);
  }
}

void cpp_typecheckt::typecheck_friend_declaration(
  symbolt &symbol,
  cpp_declarationt &declaration)
{
  // A friend of a class can be a function/method,
  // or a struct/class/union type.

  if(declaration.is_template())
  {
    // Friend template class declaration: grant access to all
    // instantiations of the named template.
    if(declaration.declarators().empty())
    {
      typet &ftype = declaration.type();
      if(ftype.id() == ID_struct || ftype.id() == ID_union)
      {
        cpp_save_scopet saved_scope(cpp_scopes);
        cpp_scopes.go_to_global_scope();
        typecheck_type(ftype);
        symbol.type.add(ID_C_friends).move_to_sub(ftype);
      }
    }
    return;
  }

  // we distinguish these whether there is a declarator
  if(declaration.declarators().empty())
  {
    typet &ftype = declaration.type();

    // must be struct or union
    if(ftype.id() != ID_struct && ftype.id() != ID_union)
    {
      error().source_location = declaration.type().source_location();
      error() << "unexpected friend" << eom;
      throw 0;
    }

    if(ftype.find(ID_body).is_not_nil())
    {
      error().source_location = declaration.type().source_location();
      error() << "friend declaration must not have compound body" << eom;
      throw 0;
    }

    cpp_save_scopet saved_scope(cpp_scopes);
    cpp_scopes.go_to_global_scope();
    typecheck_type(ftype);
    symbol.type.add(ID_C_friends).move_to_sub(ftype);

    return;
  }

  // It should be a friend function.
  // Do the declarators.

#ifdef DEBUG
  std::cout << "friend declaration: " << declaration.pretty() << '\n';
#endif

  for(auto &sub_it : declaration.declarators())
  {
#ifdef DEBUG
    std::cout << "decl: " << sub_it.pretty() << "\n with value "
              << sub_it.value().pretty() << '\n';
    std::cout << "  scope: " << cpp_scopes.current_scope().prefix << '\n';
#endif

    if(sub_it.value().is_not_nil())
    {
      // Handle = default on friend functions (e.g., friend operator==)
      if(
        sub_it.value().id() == ID_code &&
        to_code(sub_it.value()).get_statement() == ID_default)
      {
        sub_it.value() = codet(ID_block);
        sub_it.value().add_source_location() = declaration.source_location();
      }
      declaration.member_spec().set_inline(true);
    }

    cpp_declarator_convertert cpp_declarator_converter(*this);
    cpp_declarator_converter.is_friend = true;
    const symbolt &conv_symb = cpp_declarator_converter.convert(
      declaration.type(),
      declaration.storage_spec(),
      declaration.member_spec(),
      sub_it);
    exprt symb_expr = cpp_symbol_expr(conv_symb);
    symbol.type.add(ID_C_friends).move_to_sub(symb_expr);
  }
}

void cpp_typecheckt::typecheck_compound_body(symbolt &symbol)
{
  ++compound_body_depth;

  cpp_save_scopet saved_scope(cpp_scopes);

  // enter scope of compound
  cpp_scopes.set_scope(symbol.name);

  PRECONDITION(symbol.type.id() == ID_struct || symbol.type.id() == ID_union);

  struct_union_typet &type = to_struct_union_type(symbol.type);

  // Per N5008 [class.name]/1: "the class-name is also inserted into
  // the scope of the class itself; this is known as the
  // injected-class-name" — the class name is in scope from the
  // declarative-region of its definition.  Set `ID_name` (and
  // collapse the parser's cpp_name `ID_tag` into the resolved
  // symbol name) BEFORE doing any base or member elaboration.  If
  // base resolution then throws (e.g. a base-class template
  // instantiation can't complete), downstream consumers can at
  // least recognise the struct by its `ID_name` rather than
  // crashing on an empty identifier in
  // `cpp_scopes.set_scope("")`.  This is the architectural
  // ordering fix for Category A in the 2026-05-17 review.
  symbol.type.set(ID_name, symbol.name);
  if(symbol.type.find(ID_tag).id() == ID_cpp_name)
    symbol.type.set(ID_tag, symbol.base_name);

  // pull the base types in
  if(!type.find(ID_bases).get_sub().empty())
  {
    if(type.id() == ID_union)
    {
      error().source_location = symbol.location;
      error() << "union types must not have bases" << eom;
      throw 0;
    }

    // Per N5008 [class.derived]/2 + [temp.inst]/3: failure to
    // elaborate one base class (e.g. a class template
    // specialization whose body cannot complete because of an
    // upstream depth/structural limit, or a dependent base name
    // that resolves to an incomplete struct) must not abandon
    // the entire derived class.  The derived class still has its
    // own declarative region per [basic.scope.class] and its
    // body members are independently observable.  Mark the type
    // with `#unresolved_base` so downstream consumers
    // (constructor synthesis, vtable walk, member-name lookup
    // via inheritance) can skip the inherited-member work
    // gracefully and continue body elaboration here.
    //
    // ONLY APPLY DURING TEMPLATE INSTANTIATION
    // (`!instantiation_stack.empty()`): user-code class
    // declarations like
    //   `struct D : virtual B, virtual C { };  // non-virtual A
    //                                          // multi-inherit`
    // are intentional compile errors per [class.mi]/2 and the
    // user expects CBMC to refuse them with `CONVERSION ERROR`,
    // not silently recover.  See the
    // `regression/cbmc-cpp/Multiple_Inheritance3` test for the
    // canonical case.  Recovery is only meaningful for
    // libstdc++ / CBMC-internal template specializations
    // whose elaboration fails due to CBMC's depth/structural
    // limits, not the user's intent.
    //
    // This is the architectural fix for Category A-deep
    // (`cpp-frontend-review-2026-05-17.md`): irept and 61 other
    // src/util/ classes inherit from a class template whose
    // instantiation fails on libstdc++; pre-recovery the throw
    // escaped `typecheck_compound_body`, leaving the class with
    // ID_name set but zero registered components.  Consequence:
    // 62 dog-food failures with "symbol X is unknown" on member
    // access.  Recovery here keeps the body loop running so
    // members register normally.
    const bool allow_recovery = !instantiation_stack.empty();
    const std::size_t errors_before =
      get_message_handler().get_message_count(messaget::M_ERROR);
    // Save state of the current class scope's `secondary_scopes`
    // vector so we can roll back any partial additions made by
    // `typecheck_compound_bases` before the throw.  Without this
    // rollback, dangling secondary-scope pointers persist on the
    // class scope and method bodies typechecked later may walk
    // into freed/uninitialised cpp_idt nodes.
    const std::size_t saved_secondary_count =
      cpp_scopes.current_scope().secondary_scopes_size();
    const std::size_t saved_using_count =
      cpp_scopes.current_scope().using_scopes_size();
    try
    {
      typecheck_compound_bases(to_struct_type(type));
    }
    catch(...)
    {
      if(!allow_recovery)
        throw;
      get_message_handler().set_message_count(messaget::M_ERROR, errors_before);
      // Roll back partial scope linkage.
      cpp_scopes.current_scope().truncate_secondary_scopes(
        saved_secondary_count);
      cpp_scopes.current_scope().truncate_using_scopes(saved_using_count);

      symbol.type.set(ID_C_unresolved_base, true);
      // The throw escaped mid-processing of the bases array;
      // entries beyond the failure point may be unresolved
      // cpp_names rather than the post-resolution `ID_base`
      // exprs that downstream consumers (constructor synthesis,
      // vtable walk, member-name lookup via inheritance)
      // require.  Clear the array entirely — the class is
      // recovered as if it had no base classes.
      symbol.type.add(ID_bases).get_sub().clear();
    }
  }

  exprt &body = static_cast<exprt &>(type.add(ID_body));
  struct_union_typet::componentst &components = type.components();

  // (`set(ID_name, symbol.name)` already done above before bases.)

  // default access
  irep_idt access = type.default_access();

  bool found_ctor = false;
  bool found_dtor = false;

  // we first do everything _but_ the constructors

  Forall_operands(it, body)
  {
    if(it->id() == ID_cpp_declaration)
    {
      cpp_declarationt &declaration = to_cpp_declaration(*it);

      if(declaration.member_spec().is_friend())
      {
        typecheck_friend_declaration(symbol, declaration);
        continue; // done
      }

      if(declaration.is_template())
      {
        if(declaration.is_constructor())
        {
          found_ctor = true;
          // Mark the struct as having a constructor so cpp_is_pod
          // returns false even though the constructor is a template
          // and not stored as a regular component.
          symbol.type.set("has_template_constructor", true);
        }
        else if(declaration.type().id() == "cpp-cast-operator")
        {
          // Phase 4B target-type-threading: mark classes with
          // template conversion operators so
          // `user_defined_conversion_sequence` can find them when
          // looking for [temp.deduct.conv]/1 candidates.  Mirrors
          // `has_template_constructor` above.
          symbol.type.set("has_template_conversion_operator", true);
        }
        // remember access mode
        declaration.set(ID_C_access, access);
        // Per [temp.inst]/11: failure to convert one template member
        // during class instantiation should not abort processing of
        // siblings.  Catch and continue.
        if(!instantiation_stack.empty())
        {
          const std::size_t errors_before =
            get_message_handler().get_message_count(messaget::M_ERROR);
          try
          {
            convert_template_declaration(declaration);
          }
          catch(...)
          {
            get_message_handler().set_message_count(
              messaget::M_ERROR, errors_before);
          }
        }
        else
        {
          convert_template_declaration(declaration);
        }
        continue;
      }

      if(declaration.type().id().empty())
        continue;

      bool is_typedef = declaration.is_typedef();

      // is it tag-only?
      if(
        declaration.type().id() == ID_struct ||
        declaration.type().id() == ID_union ||
        declaration.type().id() == ID_c_enum)
        if(declaration.declarators().empty())
          declaration.type().set(ID_C_tag_only_declaration, true);

      declaration.name_anon_struct_union();
      // Per [class.mem]/4 and [temp.inst]/2: the type of a data
      // member must be complete at the closing `}` of the class.
      // If `typecheck_type` on the declaration's base type throws
      // *during* class body processing, the remainder of the
      // compound body loop is abandoned and the data member does
      // not register in the class scope.  That in turn causes
      // sibling method bodies to fail name lookup when
      // `typecheck_method_bodies` runs later (the classic MSVC
      // atomic_flag::_Storage failure: methods declared before the
      // data member reference it; _Storage's type `atomic<long>`
      // fails to typecheck; atomic_flag's class body is abandoned
      // with _Storage unregistered; later test_and_set's body
      // emits `symbol '_Storage' is unknown`).
      //
      // Narrow mitigation: when the type is specifically an
      // unresolved class-template specialization (cpp_name with a
      // template_args sub-element) inside a plain class body,
      // catch the failure and keep the unresolved cpp_name so the
      // declarator loop can still register the member by name.
      // Method bodies that access the member get a resolvable
      // identifier; only uses that require the concrete type fail.
      bool type_is_tpl_cpp_name = false;
      if(declaration.type().id() == ID_cpp_name)
      {
        for(const auto &sub : declaration.type().get_sub())
          if(sub.id() == ID_template_args)
          {
            type_is_tpl_cpp_name = true;
            break;
          }
      }
      bool kept_unresolved_cpp_name = false;
      if(instantiation_stack.empty() && type_is_tpl_cpp_name)
      {
        const std::size_t errors_before =
          get_message_handler().get_message_count(messaget::M_ERROR);
        typet saved_type = declaration.type();
        try
        {
          typecheck_type(declaration.type());
        }
        catch(...)
        {
          get_message_handler().set_message_count(
            messaget::M_ERROR, errors_before);
          declaration.type() = saved_type; // keep unresolved cpp_name
          kept_unresolved_cpp_name = true;
        }
      }
      else if(!instantiation_stack.empty() && type_is_tpl_cpp_name)
      {
        // [temp.inst]/3 semantics applied to member-declaration
        // elaboration: a class-template specialization's body may
        // declare members whose type is a metafunction
        // specialization over the class currently being elaborated
        // (e.g. `common_type_t<duration>` in MSVC `<chrono>`'s
        // duration, or `rebind<T>` inside an allocator).  Such
        // self-references can only resolve after the enclosing
        // class is fully elaborated; substitution now would either
        // fail or recurse.
        //
        // Per [temp.inst]/3 "the implicit instantiation of a class
        // template specialization causes the implicit instantiation
        // of the declarations, but not of the definitions, of the
        // non-deleted class member functions" — i.e. the standard
        // already expects the compiler to be tolerant of incomplete
        // member declarations during class-body elaboration.
        //
        // Detect the self-reference by scanning the member's type
        // for any `cpp_name` whose base matches the current class's
        // unqualified base name.  On failure, skip the declaration;
        // a later re-elaboration pass picks it up once the
        // dependent metafunction can resolve.  This generalizes the
        // earlier duration-only mitigation (commit 2e8e74f8ed) to
        // any class whose body contains self-referential metafunction
        // specializations.
        const std::string cur = id2string(symbol.name);
        std::string cur_head = cur;
        {
          std::size_t lt = cur_head.find('<');
          if(lt != std::string::npos)
            cur_head = cur_head.substr(0, lt);
        }
        std::string cur_base = cur_head;
        {
          std::size_t pos = cur_head.rfind("::tag-");
          if(pos != std::string::npos)
            cur_base = cur_head.substr(pos + 6);
          else
          {
            pos = cur_head.rfind("::");
            if(pos != std::string::npos)
              cur_base = cur_head.substr(pos + 2);
          }
        }
        bool is_self_reference = false;
        if(!cur_base.empty())
        {
          std::function<bool(const irept &)> ref_to_self;
          ref_to_self = [&](const irept &t) -> bool
          {
            if(t.id() == ID_cpp_name)
            {
              const auto &s = t.get_sub();
              if(!s.empty() && s.front().id() == ID_name)
              {
                const irep_idt &bn = s.front().get(ID_identifier);
                if(!bn.empty() && id2string(bn) == cur_base)
                  return true;
              }
            }
            for(const auto &x : t.get_sub())
              if(ref_to_self(x))
                return true;
            for(const auto &x : t.get_named_sub())
              if(ref_to_self(x.second))
                return true;
            return false;
          };
          is_self_reference = ref_to_self(declaration.type());
        }
        if(is_self_reference)
        {
          // Per [temp.inst]/3 + [temp.deduct]/8: elaborate under a
          // SFINAE immediate-context guard; on failure, skip the
          // declaration and let a later pass retry.
          const typet saved_self_ref_type = declaration.type();
          try
          {
            sfinae_contextt sfinae_guard{*this};
            typecheck_type(declaration.type());
          }
          catch(...)
          {
            // [temp.inst]/1-2 + [dcl.typedef]: a member typedef declares
            // the member and forms the aliased type but does not require
            // the aliased template's *definition* to be instantiated -- a
            // typedef-name may denote an incomplete type.  When the alias
            // is self-referential and cannot be eagerly instantiated while
            // the enclosing class is still incomplete (e.g. libstdc++
            // vector's `typedef __normal_iterator<const_pointer, vector>
            // const_iterator;`), keep the unresolved alias so the typedef
            // NAME is still declared (lazily) and sibling members that
            // refer to it -- such as
            // `typedef reverse_iterator<const_iterator>
            // const_reverse_iterator;` -- resolve, rather than dropping it
            // and producing a spurious "symbol 'const_iterator' is
            // unknown".  Non-typedef self-references keep the previous
            // skip-and-retry behaviour.
            if(is_typedef)
            {
              declaration.type() = saved_self_ref_type;
              kept_unresolved_cpp_name = true;
            }
            else
              continue;
          }
        }
        else if(is_typedef)
        {
          // Per [temp.inst]/1-2 and [dcl.typedef]: a member typedef
          // aliasing a class-template-id (e.g.
          // `typedef std::reverse_iterator<const_iterator>
          //  const_reverse_iterator;` in libstdc++ `basic_string`)
          // declares the member and forms the aliased type, but does
          // not require that template's *definition* to be instantiated
          // -- a typedef-name may denote an incomplete type.  Eagerly
          // instantiating the definition here can throw (at C++20 the
          // iterator-concept chain reached through `reverse_iterator`'s
          // body does); an unguarded failure abandons the rest of the
          // class body, dropping every later member including the
          // constructors.  The class is then non-conformantly
          // misclassified as a POD ([class.prop]: a class with
          // user-declared constructors is not a POD), so e.g.
          // `std::string s("ab")` is routed to a bogus `char[]` ->
          // `basic_string` conversion instead of a constructor call.
          //
          // Recover by keeping the unresolved alias (a lazy typedef)
          // rather than dropping it: a plain skip would leave later
          // members that name the alias (e.g.
          // `const_reverse_iterator rbegin() const;`) dangling and throw
          // again, re-truncating the class.  Keeping the name lets the
          // body -- and the constructors -- complete, so the class is
          // conformantly non-POD with its full member set.  (The
          // aliased template's definition is still instantiated later,
          // on demand, when its completeness is actually required.)
          const std::size_t errors_before =
            get_message_handler().get_message_count(messaget::M_ERROR);
          const typet saved_member_type = declaration.type();
          try
          {
            typecheck_type(declaration.type());
          }
          catch(...)
          {
            get_message_handler().set_message_count(
              messaget::M_ERROR, errors_before);
            declaration.type() = saved_member_type; // keep unresolved alias
            kept_unresolved_cpp_name = true;
          }
        }
        else
        {
          typecheck_type(declaration.type());
        }
      }
      else
      {
        // Per N5008 [class.mem]/3 + [temp.inst]: the
        // member-specification declares the full set of members of
        // the class.  A failure to elaborate one member's type must
        // not silently drop sibling member-declarations or
        // access-specifiers from the class body.  If the type is an
        // inline class/struct/union/enum definition (i.e., a nested
        // type whose definition is given here) and its elaboration
        // throws — typically because a base-class template
        // specialization in the inline definition fails to
        // instantiate against CBMC's libstdc++ model — the existing
        // unprotected call below would propagate the throw out of
        // the body loop, causing every subsequent member declaration
        // (and `cpp-public`/`cpp-protected` access specifiers) to be
        // silently abandoned.  The visible symptom is the classic
        // `symbol 'message_handler' is unknown` failure on CBMC's
        // own `messaget` class: its `class mstreamt : public
        // std::ostringstream` inline definition's elaboration aborts
        // the body loop, so every later `protected:` plus its data
        // members get dropped from the class scope.  Method bodies
        // that reference the dropped data members then fail name
        // lookup at typecheck-method-bodies time.
        //
        // Wrap the elaboration in a try/catch, mirroring the
        // existing `kept_unresolved_cpp_name` pattern above: reset
        // the error count and `continue;` to the next body item.
        // The nested type is unusable downstream — references to it
        // fail at their use site — but the body loop completes,
        // sibling members register, and access transitions are
        // preserved.
        //
        // Apply the recovery only when this is a NESTED inline
        // definition AND it has a base-clause.  Inline definitions
        // without bases (`class X { /* ... */ };`) cannot trigger
        // the libstdc++ instantiation-chain failure that motivates
        // the recovery, and keeping the strict behaviour for them
        // means that genuine member-elaboration errors in plain
        // user code still surface clearly.  This pattern matches
        // the libstdc++ recovery use case (a nested class derived
        // from a template specialization whose model is incomplete)
        // without relaxing diagnostics for ordinary class members.
        bool inline_def_with_base = false;
        if(
          declaration.type().id() == ID_struct ||
          declaration.type().id() == ID_union)
        {
          const irept &bases = declaration.type().find(ID_bases);
          if(!bases.get_sub().empty())
            inline_def_with_base = true;
        }

        if(instantiation_stack.empty() && inline_def_with_base)
        {
          const std::size_t errors_before =
            get_message_handler().get_message_count(messaget::M_ERROR);
          try
          {
            typecheck_type(declaration.type());
          }
          catch(...)
          {
            get_message_handler().set_message_count(
              messaget::M_ERROR, errors_before);
            continue;
          }
        }
        else if(
          is_typedef && !instantiation_stack.empty() &&
          !declaration.declarators().empty() &&
          declaration.declarators().front().name().get_base_name() ==
            "iterator_concept")
        {
          // Per [iterator.concepts.general] + [iterator.traits]: among an
          // iterator type's member typedefs, the C++20 `iterator_concept`
          // member is used *solely* for concept-based algorithm dispatch
          // (ITER_CONCEPT); unlike the five required associated types
          // (value_type, difference_type, pointer, reference,
          // iterator_category) no member function or sibling member depends
          // on it structurally.  In libstdc++ it is
          //   using iterator_concept = std::__detail::__iter_concept<_Iterator>;
          // a `merged_type` alias-template result, so the cpp_name
          // self-reference recovery above does not apply to it.
          //
          // Per [temp.inst]/1-2 + [dcl.typedef]: this member typedef declares
          // the member and forms the aliased type but does not require the
          // aliased template's *definition* to be instantiated; a typedef-name
          // may denote an incomplete type.  While the enclosing iterator
          // instance is still being completed, evaluating __iter_concept
          // reaches back through this very (incomplete) iterator via the
          // iterator-concept machinery and throws.  An unguarded failure here
          // would abandon the rest of the class body, dropping every later
          // member including the member *functions* (operator*, base,
          // operator++, ...) and leaving the instance complete-looking but
          // method-less, so a later odr-use of a method finds "no body".
          // Keep this one inert concept-dispatch alias lazy and continue, so
          // the sibling methods register; its definition is instantiated
          // later, on demand, when its completeness is actually required.
          //
          // This recovery is deliberately limited to `iterator_concept`: a
          // failure to form one of the *required* associated-type typedefs
          // signals that the instance genuinely cannot be completed yet, and
          // keeping such a type lazy would mis-instantiate the methods and
          // constructors that depend on it (observed on std::span, whose
          // iterator's required typedefs fail at this point) -- those retain
          // the strict abandon-and-retry behaviour.
          const std::size_t errors_before =
            get_message_handler().get_message_count(messaget::M_ERROR);
          const typet saved_member_type = declaration.type();
          try
          {
            typecheck_type(declaration.type());
          }
          catch(...)
          {
            get_message_handler().set_message_count(
              messaget::M_ERROR, errors_before);
            declaration.type() = saved_member_type; // keep unresolved alias
            kept_unresolved_cpp_name = true;
          }
        }
        else
        {
          typecheck_type(declaration.type());
        }
      }
      bool is_static = declaration.storage_spec().is_static();
      bool is_mutable = declaration.storage_spec().is_mutable();

      if(
        declaration.storage_spec().is_extern() ||
        declaration.storage_spec().is_register())
      {
        error().source_location = declaration.storage_spec().location();
        error() << "invalid storage class specified for field" << eom;
        throw 0;
      }

      // In C++11, 'auto' in a class member declaration indicates a
      // trailing return type (auto f() -> T). The parser stores this
      // in the storage spec. Only reject 'auto' when there are no
      // declarators (i.e., it's not a function declaration).
      if(
        declaration.storage_spec().is_auto() &&
        declaration.declarators().empty())
      {
        error().source_location = declaration.storage_spec().location();
        error() << "invalid storage class specified for field" << eom;
        throw 0;
      }

      // anonymous member?
      if(
        declaration.declarators().empty() &&
        ((declaration.type().id() == ID_struct_tag &&
          follow_tag(to_struct_tag_type(declaration.type()))
            .get_bool(ID_C_is_anonymous)) ||
         (declaration.type().id() == ID_union_tag &&
          follow_tag(to_union_tag_type(declaration.type()))
            .get_bool(ID_C_is_anonymous)) ||
         declaration.type().get_bool(ID_C_is_anonymous)))
      {
        // we only allow this on struct/union types
        if(
          declaration.type().id() != ID_union_tag &&
          declaration.type().id() != ID_struct_tag)
        {
          error().source_location = declaration.type().source_location();
          error() << "member declaration does not declare anything" << eom;
          throw 0;
        }

        convert_anon_struct_union_member(declaration, access, components);

        continue;
      }

      // declarators
      for(auto &declarator : declaration.declarators())
      {
        // Skip the constructors until all the data members
        // are discovered
        if(declaration.is_destructor())
          found_dtor = true;

        if(declaration.is_constructor())
        {
          found_ctor = true;
          continue;
        }

        // Per [temp.res] and [temp.inst]/11: type-checking a member
        // declaration during class template instantiation may fail
        // because a dependent name cannot be resolved in the current
        // instantiation context (for example
        //   typedef typename __alloc_traits::pointer pointer;
        // when __alloc_traits itself requires further instantiation).
        // The failure is local to the member being processed; letting
        // sibling members continue lets the class scope accumulate
        // the typedefs/members that do not depend on the failing one.
        if(!instantiation_stack.empty())
        {
          const std::size_t errors_before =
            get_message_handler().get_message_count(messaget::M_ERROR);
          try
          {
            typecheck_compound_declarator(
              symbol,
              declaration,
              declarator,
              components,
              access,
              is_static,
              is_typedef,
              is_mutable);
          }
          catch(...)
          {
            get_message_handler().set_message_count(
              messaget::M_ERROR, errors_before);
          }
        }
        else if(kept_unresolved_cpp_name)
        {
          // Phase 3 narrow producer per N5008 [temp.inst]/3.1.  The
          // existing `kept_unresolved_cpp_name` mitigation upstream
          // preserved the unresolved cpp_name on the declaration so
          // a non-typedef data-member declarator can still register.
          // Below we handle the additional case where
          // `typecheck_compound_declarator` *itself* fails — most
          // commonly on a `typedef T name;` form whose aliased
          // template type cannot be eagerly instantiated.  Without
          // recovery, the throw escapes `typecheck_compound_body`
          // and abandons the entire class scope, preventing sibling
          // members and methods from registering even when they
          // don't depend on the failing typedef.  Instead we register
          // the typedef lazily: a typedef symbol with the unresolved
          // cpp_name as its alias type, marked `ID_C_lazy_member_type`,
          // and put into the class scope.  Lookups of the typedef
          // succeed structurally; uses that need the resolved
          // template instantiation still fail but only at the use
          // site, with a localized diagnostic.
          const std::size_t errors_before =
            get_message_handler().get_message_count(messaget::M_ERROR);
          try
          {
            typecheck_compound_declarator(
              symbol,
              declaration,
              declarator,
              components,
              access,
              is_static,
              is_typedef,
              is_mutable);
          }
          catch(...)
          {
            get_message_handler().set_message_count(
              messaget::M_ERROR, errors_before);
            const auto &name_sub = declarator.name().get_sub();
            if(name_sub.empty())
              throw;
            const irep_idt base_name = name_sub.front().get(ID_identifier);
            if(base_name.empty())
              throw;

            // Capture the class-scope identifier for later
            // re-resolution by `ensure_member_complete`: the helper
            // needs to switch into this scope to give member-typedef
            // resolution a chance.  Also capture the unresolved
            // cpp_name so the source survives the `declaration.type()`
            // being mutated by other declarators in the same
            // declaration list.
            const irep_idt class_scope_id =
              cpp_scopes.current_scope().identifier;
            typet lazy_source = declaration.type();

            if(is_typedef)
            {
              // Lazy typedef registration.  Build the symbol the
              // way `cpp_declarator_convertert` would, but with the
              // unresolved cpp_name preserved as the aliased type
              // and the lazy marker so callers know to retry
              // resolution at the use site (see
              // `cpp_typecheckt::ensure_member_complete`).
              const irep_idt sym_name =
                id2string(cpp_scopes.current_scope().prefix) +
                id2string(base_name);
              if(!symbol_table.has_symbol(sym_name))
              {
                symbolt typedef_sym;
                typedef_sym.name = sym_name;
                typedef_sym.base_name = base_name;
                typedef_sym.pretty_name = base_name;
                typedef_sym.type = lazy_source;
                typedef_sym.type.set(ID_C_lazy_member_type, true);
                typedef_sym.type.set(ID_lazy_type_source, class_scope_id);
                typedef_sym.location = declarator.source_location();
                typedef_sym.mode = ID_cpp;
                typedef_sym.module = module;
                typedef_sym.is_type = true;
                typedef_sym.is_macro = true;
                if(symbol_table.insert(std::move(typedef_sym)).second)
                {
                  cpp_idt &id = cpp_scopes.put_into_scope(
                    symbol_table.lookup_ref(sym_name));
                  id.id_class = cpp_idt::id_classt::TYPEDEF;
                }
              }

              struct_typet::componentt comp(base_name, lazy_source);
              comp.set_base_name(base_name);
              comp.set(ID_access, access);
              comp.set(ID_is_type, true);
              comp.set(ID_C_lazy_member_type, true);
              comp.set(ID_lazy_type_source, class_scope_id);
              comp.add_source_location() = declarator.source_location();
              components.push_back(std::move(comp));
            }
            else
            {
              struct_typet::componentt comp(base_name, lazy_source);
              comp.set_base_name(base_name);
              comp.set(ID_access, access);
              if(is_static)
                comp.set(ID_is_static, true);
              if(is_mutable)
                comp.set(ID_is_mutable, true);
              comp.set(ID_C_lazy_member_type, true);
              comp.set(ID_lazy_type_source, class_scope_id);
              comp.add_source_location() = declarator.source_location();
              components.push_back(std::move(comp));
            }
          }
        }
        else
        {
          typecheck_compound_declarator(
            symbol,
            declaration,
            declarator,
            components,
            access,
            is_static,
            is_typedef,
            is_mutable);
        }
      }
    }
    else if(it->id() == "cpp-public")
      access = ID_public;
    else if(it->id() == "cpp-private")
      access = ID_private;
    else if(it->id() == "cpp-protected")
      access = ID_protected;
    else if(it->id() == ID_cpp_using)
    {
      cpp_usingt &cpp_using =
        static_cast<cpp_usingt &>(static_cast<irept &>(*it));
      // Skip using declarations for conversion operators (e.g.,
      // using Base::operator T;) as these are not yet supported.
      bool has_operator = false;
      for(const auto &sub : cpp_using.name().get_sub())
      {
        if(sub.id() == ID_operator)
        {
          has_operator = true;
          break;
        }
      }
      if(has_operator)
      {
        // using Base::operator X — import operator from base class.
        // Resolve the base class and copy matching operator components
        // into the derived class.
        try
        {
          convert(cpp_using);
        }
        catch(...)
        {
          // Operator import failed (e.g., base class not fully
          // instantiated in CRTP patterns). Silently skip.
        }
      }
      else
      {
        // C++11 inheriting constructors: using Base::Base;
        // Detect if this refers to a base class constructor and skip
        // the normal convert() path which fails on constructor lookup.
        bool is_inheriting_ctor = false;
        const auto &name_sub = cpp_using.name().get_sub();
        if(name_sub.size() >= 3)
        {
          const irep_idt &last_name = name_sub.back().get(ID_identifier);
          for(const auto &base : to_struct_type(symbol.type).bases())
          {
            const symbolt &base_sym = lookup(to_struct_tag_type(base.type()));
            if(base_sym.base_name == last_name)
            {
              is_inheriting_ctor = true;
              break;
            }
          }
        }
        if(!is_inheriting_ctor)
        {
          convert(cpp_using);

          // [namespace.udecl]/19: a using-declaration that names an
          // inherited member makes that member accessible in the
          // derived class with the access of the using-declaration,
          // independent of the member's access in the base.  Adjust the
          // access of the corresponding inherited (from_base)
          // component(s) so member-access checking honours it -- e.g.
          // binary_exprt's public `using exprt::op0;` republishes the
          // protected exprt::op0 as public.
          if(cpp_using.name().is_qualified() && !name_sub.empty())
          {
            const irep_idt &member_name = name_sub.back().get(ID_identifier);
            if(!member_name.empty())
            {
              for(auto &comp : components)
              {
                if(
                  comp.get_bool(ID_from_base) &&
                  comp.get_base_name() == member_name)
                {
                  comp.set_access(access);
                }
              }
            }
          }
        }
        else
        {
          // Import base class constructors as derived class constructors
          const irep_idt &last_name = name_sub.back().get(ID_identifier);
          found_ctor = true;
          for(const auto &base : to_struct_type(symbol.type).bases())
          {
            const symbolt &base_sym = lookup(to_struct_tag_type(base.type()));
            if(base_sym.base_name != last_name)
              continue;
            for(const auto &comp : to_struct_type(base_sym.type).components())
            {
              if(comp.type().id() != ID_code)
                continue;
              const code_typet &ctor_type = to_code_type(comp.type());
              if(ctor_type.return_type().id() != ID_constructor)
                continue;
              // Skip default and copy/move constructors
              if(ctor_type.parameters().size() <= 1)
                continue;
              if(
                ctor_type.parameters().size() == 2 &&
                ctor_type.parameters()[1].type().id() == ID_pointer &&
                is_reference(ctor_type.parameters()[1].type()))
                continue;
              // Create a derived-class constructor component that
              // mirrors the base constructor
              struct_typet::componentt new_comp = comp;
              new_comp.set(ID_from_base, false);
              new_comp.set(ID_access, access);
              new_comp.set_base_name(symbol.base_name);
              components.push_back(new_comp);
            }
            break;
          }
        }
      }
    }
    else
    {
    }
  }

  // Add the default dtor, if needed
  // (we have to do the destructor before building the virtual tables,
  //  as the destructor may be virtual!)

  if((found_ctor || !cpp_is_pod(symbol.type)) && !found_dtor)
  {
    // build declaration
    cpp_declarationt dtor;
    default_dtor(symbol, dtor);

    typecheck_compound_declarator(
      symbol,
      dtor,
      dtor.declarators()[0],
      components,
      ID_public,
      false,
      false,
      false);
  }

  // set up virtual tables before doing the constructors
  if(symbol.type.id() == ID_struct)
    do_virtual_table(symbol);

  if(!found_ctor && !cpp_is_pod(symbol.type))
  {
    // C++11: the default constructor is implicitly deleted if any
    // non-static data member is a reference type.
    bool has_reference_member = false;
    for(const auto &c : to_struct_union_type(symbol.type).components())
    {
      if(
        !c.get_bool(ID_from_base) && !c.get_bool(ID_is_type) &&
        !c.get_bool(ID_is_static) && c.type().id() == ID_pointer &&
        c.type().get_bool(ID_C_reference))
      {
        has_reference_member = true;
        break;
      }
    }

    if(!has_reference_member)
    {
      // it's public!
      exprt cpp_public("cpp-public");
      body.add_to_operands(std::move(cpp_public));

      // build declaration
      cpp_declarationt ctor;
      default_ctor(symbol.type.source_location(), symbol.base_name, ctor);
      body.add_to_operands(std::move(ctor));
    }
  }

  // Reset the access type
  access = type.default_access();

  // All the data members are now known.
  // We now deal with the constructors that we are given.
  Forall_operands(it, body)
  {
    if(it->id() == ID_cpp_declaration)
    {
      cpp_declarationt &declaration = to_cpp_declaration(*it);

      if(!declaration.is_constructor())
        continue;

      // For constructor TEMPLATES, the signature may reference the
      // function template's own parameters (e.g. libstdc++'s
      // `pair(const pair<_U1, _U2>& __p)` in stl_pair.h, where _U1
      // and _U2 belong to the constructor template, not to the
      // enclosing class).  The first pass already registered the
      // template via convert_template_declaration and added the
      // template scope as a secondary scope of the class scope; that
      // makes _U1 lookup-resolvable to a TEMPLATE_PARAMETER cpp_id.
      // But `convert_template_parameter` also consults
      // `template_map`, which only has the class's parameters bound
      // (e.g. _T1=int, _T2=int).  Without an entry for _U1, the
      // lookup falls through to a silent `throw 0`, which propagates
      // out of `instantiate_template` and gets caught by the
      // enclosing `typecheck_method_bodies`, leaving the user's
      // function (e.g. `main`) half-typechecked and dropping the
      // `std::pair<int, int> p;` declaration silently.
      //
      // Populate the function template's TYPE parameters as
      // `unassigned`-typed placeholders for the duration of this
      // declarator's typecheck.  `convert_template_parameter` will
      // then return the placeholder rather than throwing.  We only
      // populate type parameters; non-type parameters whose values
      // are needed in the signature must be evaluated to actual
      // constants by the caller of the template, so we leave them
      // unbound and let the existing throw fire (and be caught) for
      // those.
      std::unique_ptr<cpp_saved_template_mapt> saved_map;
      if(declaration.is_template())
      {
        saved_map = std::make_unique<cpp_saved_template_mapt>(template_map);
        for(const auto &t : declaration.template_type().template_parameters())
        {
          if(t.id() == ID_type)
          {
            const irep_idt id = t.type().get(ID_identifier);
            if(
              !id.empty() &&
              template_map.type_map.find(id) == template_map.type_map.end())
            {
              typet placeholder{ID_unassigned};
              placeholder.set(ID_identifier, id);
              placeholder.add_source_location() = t.source_location();
              template_map.type_map[id] = placeholder;
            }
          }
        }
      }

      for(auto &declarator : declaration.declarators())
      {
#if 0
        irep_idt ctor_base_name=
          declarator.name().get_base_name();
#endif

        if(
          declarator.value().is_not_nil() &&
          to_code(declarator.value()).get_statement() != ID_cpp_delete)
        {
          if(declarator.find(ID_member_initializers).is_nil())
            declarator.set(ID_member_initializers, ID_member_initializers);

          if(type.id() == ID_union)
          {
            check_member_initializers(
              {}, type.components(), declarator.member_initializers());
          }
          else
          {
            check_member_initializers(
              to_struct_type(type).bases(),
              type.components(),
              declarator.member_initializers(),
              type.get(ID_name));
          }

          full_member_initialization(type, declarator.member_initializers());
        }

        // Finally, we typecheck the constructor with the
        // full member-initialization list
        // Shall all be false
        bool is_static = declaration.storage_spec().is_static();
        bool is_mutable = declaration.storage_spec().is_mutable();
        bool is_typedef = declaration.is_typedef();

        typecheck_compound_declarator(
          symbol,
          declaration,
          declarator,
          components,
          access,
          is_static,
          is_typedef,
          is_mutable);
      }
    }
    else if(it->id() == "cpp-public")
      access = ID_public;
    else if(it->id() == "cpp-private")
      access = ID_private;
    else if(it->id() == "cpp-protected")
      access = ID_protected;
    else
    {
    }
  }

  if(!cpp_is_pod(symbol.type))
  {
    // Add the default copy constructor
    struct_typet::componentt component;

    if(!find_cpctor(symbol))
    {
      // build declaration
      cpp_declarationt cpctor;
      default_cpctor(symbol, cpctor);
      CHECK_RETURN(cpctor.declarators().size() == 1);

      exprt value(ID_cpp_not_typechecked);
      value.copy_to_operands(cpctor.declarators()[0].value());
      cpctor.declarators()[0].value() = value;

      typecheck_compound_declarator(
        symbol,
        cpctor,
        cpctor.declarators()[0],
        components,
        ID_public,
        false,
        false,
        false);
    }

    // Add the default assignment operator
    if(!find_assignop(symbol))
    {
      // build declaration
      cpp_declarationt assignop;
      default_assignop(symbol, assignop);
      CHECK_RETURN(assignop.declarators().size() == 1);

      // The value will be typechecked only if the operator
      // is actually used
      cpp_declaratort declarator;
      assignop.declarators().push_back(declarator);
      assignop.declarators()[0].value() = exprt(ID_cpp_not_typechecked);

      typecheck_compound_declarator(
        symbol,
        assignop,
        assignop.declarators()[0],
        components,
        ID_public,
        false,
        false,
        false);
    }
  }

  // clean up!
  symbol.type.remove(ID_body);

  // Process deferred static member initializers now that all
  // members are declared.
  {
    auto deferred = std::move(deferred_static_initializers);
    deferred_static_initializers.clear();
    for(const auto &sym_name : deferred)
    {
      symbolt &sym = symbol_table.get_writeable_ref(sym_name);
      if(sym.value.is_nil())
        continue;

      if(sym.is_macro)
      {
        // Per [temp.deduct]/8 applied to constexpr-macro init:
        // initializer substitution may fail if template parameters
        // are not yet fully substituted at this deferred elaboration
        // point.  Treat as deduction failure and fall back to a
        // template_map-directed expression-walk substitution below.
        try
        {
          sfinae_contextt sfinae_guard{*this};
          c_typecheck_baset::do_initializer(sym);
        }
        catch(...)
        {
          sym.value.visit_pre(
            [this](exprt &e)
            {
              if(e.id() == ID_symbol)
              {
                exprt v =
                  template_map.lookup(to_symbol_expr(e).get_identifier());
                if(v.is_not_nil())
                  e = v;
              }
            });
        }
      }
      else
      {
        c_typecheck_baset::do_initializer(sym);
      }

      // Mark static const integral members as compile-time constants.
      if(
        !sym.is_macro && sym.type.get_bool(ID_C_constant) &&
        (sym.type.id() == ID_signedbv || sym.type.id() == ID_unsignedbv ||
         sym.type.id() == ID_bool || sym.type.id() == ID_c_bool ||
         sym.type.id() == ID_c_enum_tag))
      {
        simplify(sym.value, *this);
        if(sym.value.is_constant())
          sym.is_macro = true;
      }
    }
  }

  // Phase 4 end-of-body resolution sweep per N5008 [temp.inst]/3.1:
  // before exiting the class body and tearing down the scope, take
  // one last pass at resolving any lazy components and the typedef
  // symbols Phase 3 may have created for them.  At this point all
  // sibling members are registered, so a forward-reference failure
  // at the original declaration site may now succeed.  For
  // structural failures (libcxx instantiation depth/limits) the
  // retry will still fail under `sfinae_contextt` and the lazy
  // marker remains; that is the correct fallback.
  //
  // We are inside the class scope here, so the helpers' own
  // re-entry guard would defer.  Instead we drive resolution
  // directly via `try_resolve_lazy_member` for components and a
  // mutable retry of `try_resolve_lazy_typedef_symbol` for typedef
  // symbols, both already wrapped in `sfinae_contextt`.  Note: for
  // the symbol path we cannot use the helper (it would defer here);
  // use the type-level helper after temporarily clearing the lazy
  // marker is also unsuitable.  Instead, bypass the re-entry guard
  // by inlining the same retry logic for components only — the
  // typedef symbols share their type with the corresponding
  // component, and updating the component is sufficient for
  // correctness in Phase 4 (the typedef symbol is updated
  // separately at first use outside the class via the
  // `try_resolve_lazy_typedef_symbol` caller in the resolver).
  for(auto &c : to_struct_union_type(symbol.type).components())
  {
    if(!c.get_bool(ID_C_lazy_member_type))
      continue;
    typet candidate = c.type();
    candidate.remove(ID_C_lazy_member_type);
    candidate.remove(ID_lazy_type_source);
    try
    {
      sfinae_contextt sfinae_guard{*this};
      typecheck_type(candidate);
      c.type() = std::move(candidate);
      // Note: the corresponding typedef symbol the producer may
      // have created is not updated here.  Its type still carries
      // the lazy markers and an incrementally different shape
      // (typedef ID_C_typedef self-reference).  Updating it here
      // proved to break downstream consumers (regression on
      // `options.cpp` and `string_container.cpp` in dog-food when
      // attempted: 14/5/98/0 → 12/5/100/0).  The typedef symbol
      // is updated separately at first use outside the class via
      // the `try_resolve_lazy_typedef_symbol` caller in the
      // resolver.
    }
    catch(...)
    {
      // Substitution failure per [temp.deduct]/8 — keep the lazy
      // placeholder for subsequent retries at use sites.
    }
  }

  --compound_body_depth;
}

void cpp_typecheckt::move_member_initializers(
  irept &initializers,
  const code_typet &type,
  exprt &value)
{
  // see if we have initializers
  if(!initializers.get_sub().empty())
  {
    const source_locationt &location = static_cast<const source_locationt &>(
      initializers.find(ID_C_source_location));

    if(type.return_type().id() != ID_constructor)
    {
      error().source_location = location;
      error() << "only constructors are allowed to "
              << "have member initializers" << eom;
      throw 0;
    }

    if(value.is_nil())
    {
      error().source_location = location;
      error() << "only constructors with body are allowed to "
              << "have member initializers" << eom;
      throw 0;
    }

    if(to_code(value).get_statement() != ID_block)
      value = code_blockt{{to_code(value)}};

    exprt::operandst::iterator o_it = value.operands().begin();
    for(const auto &initializer : initializers.get_sub())
    {
      o_it =
        value.operands().insert(o_it, static_cast<const exprt &>(initializer));
      o_it++;
    }
  }
}

void cpp_typecheckt::typecheck_member_function(
  const symbolt &compound_symbol,
  struct_typet::componentt &component,
  irept &initializers,
  const typet &method_qualifier,
  exprt &value)
{
  code_typet &type = to_code_type(component.type());

  if(component.get_bool(ID_is_static))
  {
    if(!method_qualifier.id().empty())
    {
      error().source_location = component.source_location();
      error() << "method is static -- no qualifiers allowed" << eom;
      throw 0;
    }
  }
  else
  {
    // C++23 deducing this: don't add implicit this
    if(!type.get_bool("explicit_this"))
      add_this_to_method_type(compound_symbol, type, method_qualifier);
  }

  if(value.id() == ID_cpp_not_typechecked && value.has_operands())
  {
    move_member_initializers(
      initializers, type, to_multi_ary_expr(value).op0());
  }
  else
    move_member_initializers(initializers, type, value);

  irep_idt f_id = function_identifier(component.type());

  const irep_idt identifier = cpp_scopes.current_scope().prefix +
                              id2string(component.get_base_name()) +
                              id2string(f_id);

  component.set_name(identifier);
  component.set(ID_prefix, id2string(identifier) + "::");

  if(value.is_not_nil())
    to_code_type(type).set_inlined(true);

  symbolt symbol{identifier, type, compound_symbol.mode};
  symbol.base_name = component.get_base_name();
  symbol.value.swap(value);
  symbol.module = module;
  symbol.location = component.source_location();

  // move early, it must be visible before doing any value
  symbolt *new_symbol;

  const bool symbol_exists = symbol_table.move(symbol, new_symbol);
  if(symbol_exists && new_symbol->is_weak)
  {
    // there might have been an earlier friend declaration
    *new_symbol = std::move(symbol);
  }
  else if(symbol_exists)
  {
    // A template constructor instantiation may produce the same signature
    // as an existing non-template constructor (e.g., template<typename U>
    // allocator(const allocator<U>&) instantiated with U matching T
    // collides with the copy constructor). In that case, keep the existing
    // symbol.
    if(
      new_symbol->type.id() == ID_code &&
      to_code_type(new_symbol->type).return_type().id() == ID_constructor)
    {
      return;
    }

    // A template method may be instantiated multiple times with the same
    // signature when different template arguments produce the same type.
    // Keep the existing symbol.
    if(new_symbol->type == symbol.type)
    {
      return;
    }

    // Different template instantiations of the same method template may
    // produce different return types but identical parameter types (e.g.,
    // template<typename T> static T test(int) instantiated with int and
    // long). The function_identifier only encodes parameter types, so
    // these collide. Keep the existing symbol.
    if(
      new_symbol->type.id() == ID_code && symbol.type.id() == ID_code &&
      to_code_type(new_symbol->type).parameters() ==
        to_code_type(symbol.type).parameters())
    {
      return;
    }

    error().source_location = symbol.location;
    error() << "failed to insert new method symbol: " << symbol.name << '\n'
            << "name of previous symbol: " << new_symbol->name << '\n'
            << "location of previous symbol: " << new_symbol->location << eom;

    throw 0;
  }

  // Is this in a class template?
  // If so, we defer typechecking until used.
  // But for template INSTANTIATIONS (template_class_instance),
  // the methods should be processed — they ARE being used.
  if(
    cpp_scopes.current_scope().get_parent().is_template_scope() &&
    !symbol.type.get_bool(ID_template_class_instance))
  {
    deferred_typechecking.insert(new_symbol->name);
  }
  else
    add_method_body(new_symbol);
}

void cpp_typecheckt::add_this_to_method_type(
  const symbolt &compound_symbol,
  code_typet &type,
  const typet &method_qualifier)
{
  typet subtype;

  if(compound_symbol.type.id() == ID_union)
    subtype = union_tag_typet(compound_symbol.name);
  else
    subtype = struct_tag_typet(compound_symbol.name);

  if(has_const(method_qualifier))
    subtype.set(ID_C_constant, true);

  if(has_volatile(method_qualifier))
    subtype.set(ID_C_volatile, true);

  code_typet::parametert parameter(pointer_type(subtype));
  parameter.set_identifier(ID_this);
  parameter.set_base_name(ID_this);
  parameter.set_this();
  if(!cpp_scopes.current_scope().get_parent().is_template_scope())
    convert_parameter(compound_symbol.mode, parameter);

  code_typet::parameterst &parameters = type.parameters();
  parameters.insert(parameters.begin(), parameter);
}

void cpp_typecheckt::add_anonymous_members_to_scope(
  const symbolt &struct_union_symbol)
{
  const struct_union_typet &struct_union_type =
    to_struct_union_type(struct_union_symbol.type);

  const struct_union_typet::componentst &struct_union_components =
    struct_union_type.components();

  // do scoping -- the members of the struct/union
  // should be visible in the containing struct/union,
  // and that recursively!

  for(const auto &comp : struct_union_components)
  {
    if(comp.type().id() == ID_code)
    {
      error().source_location = struct_union_symbol.type.source_location();
      error() << "anonymous struct/union member '"
              << struct_union_symbol.base_name
              << "' shall not have function members" << eom;
      throw 0;
    }

    if(comp.get_anonymous())
    {
      const symbolt &symbol = lookup(comp.type().get(ID_identifier));
      // recursive call
      add_anonymous_members_to_scope(symbol);
    }
    else
    {
      const irep_idt &base_name = comp.get_base_name();

      if(cpp_scopes.current_scope().contains(base_name))
      {
        error().source_location = comp.source_location();
        error() << "'" << base_name << "' already in scope" << eom;
        throw 0;
      }

      cpp_idt &id = cpp_scopes.current_scope().insert(base_name);
      id.id_class = cpp_idt::id_classt::SYMBOL;
      id.identifier = comp.get_name();
      id.class_identifier = struct_union_symbol.name;
      id.is_member = true;
    }
  }
}

void cpp_typecheckt::convert_anon_struct_union_member(
  const cpp_declarationt &declaration,
  const irep_idt &access,
  struct_typet::componentst &components)
{
  const struct_union_typet &final_type =
    declaration.type().id() == ID_struct_tag
      ? static_cast<const struct_union_typet &>(
          follow_tag(to_struct_tag_type(declaration.type())))
      : static_cast<const struct_union_typet &>(
          follow_tag(to_union_tag_type(declaration.type())));
  symbolt &struct_union_symbol =
    symbol_table.get_writeable_ref(final_type.get(ID_name));

  if(
    declaration.storage_spec().is_static() ||
    declaration.storage_spec().is_mutable())
  {
    error().source_location = struct_union_symbol.type.source_location();
    error() << "storage class is not allowed here" << eom;
    throw 0;
  }

  if(!cpp_is_pod(struct_union_symbol.type))
  {
    error().source_location = struct_union_symbol.type.source_location();
    error() << "anonymous struct/union member is not POD" << eom;
    throw 0;
  }

  // produce an anonymous member
  irep_idt base_name = "#anon_member" + std::to_string(components.size());

  irep_idt identifier = cpp_scopes.current_scope().prefix + base_name.c_str();

  typet compound_type;

  if(struct_union_symbol.type.id() == ID_union)
    compound_type = union_tag_typet(struct_union_symbol.name);
  else
    compound_type = struct_tag_typet(struct_union_symbol.name);

  struct_typet::componentt component(identifier, compound_type);
  component.set_access(access);
  component.set_base_name(base_name);
  component.set_pretty_name(base_name);
  component.set_anonymous(true);
  component.add_source_location() = declaration.source_location();

  components.push_back(component);

  add_anonymous_members_to_scope(struct_union_symbol);

  put_compound_into_scope(component);

  struct_union_symbol.type.set(ID_C_unnamed_object, base_name);
}

bool cpp_typecheckt::get_component(
  const source_locationt &source_location,
  const exprt &object,
  const irep_idt &component_name,
  exprt &member)
{
  PRECONDITION(
    object.type().id() == ID_struct_tag || object.type().id() == ID_union_tag);

  struct_union_typet final_type =
    object.type().id() == ID_struct_tag
      ? static_cast<const struct_union_typet &>(
          follow_tag(to_struct_tag_type(object.type())))
      : static_cast<const struct_union_typet &>(
          follow_tag(to_union_tag_type(object.type())));

  const struct_union_typet::componentst &components = final_type.components();

  for(const auto &component : components)
  {
    member_exprt tmp(object, component.get_name(), component.type());
    tmp.add_source_location() = source_location;

    if(component.get_name() == component_name)
    {
      member.swap(tmp);

      bool not_ok = check_component_access(component, final_type);
      if(not_ok)
      {
        if(disable_access_control)
        {
          member.set(ID_C_not_accessible, true);
          member.set(ID_C_access, component.get(ID_access));
        }
        else
        {
          // Allow derived class constructors to call base class
          // private constructors (e.g., MSVC's bad_array_new_length
          // calling bad_alloc(const char*)).
          const std::string file = id2string(source_location.get_file());
          if(
            file.find("include") != std::string::npos ||
            file.find("Include") != std::string::npos)
          {
            member.set(ID_C_not_accessible, true);
            member.set(ID_C_access, component.get(ID_access));
          }
          else
          {
            error().source_location = source_location;
            error() << "member '" << component_name << "' is not accessible ("
                    << component.get(ID_access) << ")" << eom;
            throw 0;
          }
        }
      }

      if(object.get_bool(ID_C_lvalue))
        member.set(ID_C_lvalue, true);

      if(
        object.type().get_bool(ID_C_constant) &&
        !component.get_bool(ID_is_mutable))
      {
        member.type().set(ID_C_constant, true);
      }

      member.add_source_location() = source_location;

      return true; // component found
    }
    else if(
      (component.type().id() == ID_struct_tag &&
       follow_tag(to_struct_tag_type(component.type()))
         .find(ID_C_unnamed_object)
         .is_not_nil()) ||
      (component.type().id() == ID_union_tag &&
       follow_tag(to_union_tag_type(component.type()))
         .find(ID_C_unnamed_object)
         .is_not_nil()) ||
      component.type().find(ID_C_unnamed_object).is_not_nil())
    {
      // could be anonymous union or struct

      if(
        component.type().id() == ID_union_tag ||
        component.type().id() == ID_struct_tag)
      {
        // recursive call!
        if(get_component(source_location, tmp, component_name, member))
        {
          if(check_component_access(component, final_type))
          {
            error().source_location = source_location;
            error() << "member '" << component_name << "' is not accessible"
                    << eom;
            throw 0;
          }

          if(object.get_bool(ID_C_lvalue))
            member.set(ID_C_lvalue, true);

          if(
            object.get_bool(ID_C_constant) &&
            !component.get_bool(ID_is_mutable))
          {
            member.type().set(ID_C_constant, true);
          }

          member.add_source_location() = source_location;
          return true; // component found
        }
      }
    }
  }

  return false; // component not found
}

bool cpp_typecheckt::check_component_access(
  const struct_union_typet::componentt &component,
  const struct_union_typet &struct_union_type)
{
  const irep_idt &access = component.get(ID_access);

  if(access == ID_public)
    return false; // ok

  const irep_idt &struct_identifier = struct_union_type.get(ID_name);

  // A member inherited from a base class is, in addition to being
  // accessible as named in the type of the object through which it is
  // used ([class.access.base]/5.2-5.3, handled via struct_identifier
  // below), accessible from the class that *declares* it and -- for a
  // protected member -- from classes derived from that declaring class
  // ([class.access.base]/5.4): a member or friend of the declaring base
  // may name the member on an object of any derived type, even when the
  // member is inaccessible (noaccess) as named through that derived
  // type.  Resolve the declaring class (the unique base carrying the
  // member without ID_from_base) and the member's access there, so both
  // can be consulted alongside the object's type.
  const struct_typet *declaring_type = nullptr;
  irep_idt declaring_access;
  if(component.get_bool(ID_from_base) && struct_union_type.id() == ID_struct)
  {
    const irep_idt &component_name = component.get_name();
    std::set<irep_idt> bases;
    get_bases(to_struct_type(struct_union_type), bases);
    for(const auto &base_name : bases)
    {
      const symbolt &base_symbol = lookup(base_name);
      if(base_symbol.type.id() != ID_struct)
        continue;
      const struct_typet &base_struct = to_struct_type(base_symbol.type);
      for(const auto &c : base_struct.components())
      {
        if(c.get_name() == component_name && !c.get_bool(ID_from_base))
        {
          declaring_type = &base_struct;
          declaring_access = c.get(ID_access);
          break;
        }
      }
      if(declaring_type != nullptr)
        break;
    }
  }

  // A non-inherited inaccessible member is genuinely inaccessible; an
  // inherited one may still be reachable from its declaring class, so
  // only bail out early when there is no declaring class to consult.
  if(access == ID_noaccess && declaring_type == nullptr)
    return true; // not ok

  for(cpp_scopet *pscope = &(cpp_scopes.current_scope());
      !(pscope->is_root_scope());
      pscope = &(pscope->get_parent()))
  {
    if(pscope->is_class())
    {
      // The declaring class may always name its own member, whatever
      // its access as seen through the object's (derived) type.
      if(
        declaring_type != nullptr &&
        pscope->identifier == declaring_type->get(ID_name))
        return false; // ok

      // Accessible as named through the object's own type (unless the
      // member is inaccessible there).
      if(access != ID_noaccess && pscope->identifier == struct_identifier)
        return false; // ok

      // The enclosing class may still be mid-elaboration (e.g. while
      // instantiating its constructor); without a complete struct
      // definition the derived-from relationships below cannot be
      // evaluated, so move on to the enclosing scope.
      const symbolt &scope_symbol = lookup(pscope->identifier);
      if(
        scope_symbol.type.id() != ID_struct ||
        to_struct_type(scope_symbol.type).is_incomplete())
      {
        if(config.cpp.cpp_standard >= configt::cppt::cpp_standardt::CPP11)
          continue;
        break;
      }

      const struct_typet &scope_struct = to_struct_type(scope_symbol.type);

      const bool derived_from_object =
        subtype_typecast(scope_struct, to_struct_type(struct_union_type));
      const bool derived_from_declaring =
        declaring_type != nullptr &&
        subtype_typecast(scope_struct, *declaring_type);

      // Protected members are accessible from classes derived from the
      // class through which they are named, resp. that declares them.
      if(
        (access == ID_protected && derived_from_object) ||
        (declaring_access == ID_protected && derived_from_declaring))
        return false; // ok

      // Compiler-generated members (e.g. vtable pointers) whose names
      // contain '@' are always accessible from derived classes.
      if(
        (derived_from_object || derived_from_declaring) &&
        id2string(component.get_name()).find('@') != std::string::npos)
        return false; // ok

      // private members are not accessible from derived classes

      // C++11 (DR 45): nested classes have access to the enclosing
      // class's private and protected members.
      if(config.cpp.cpp_standard >= configt::cppt::cpp_standardt::CPP11)
      {
        continue;
      }

      break;
    }
  }

  // check friendship
  const irept::subt &friends = struct_union_type.find(ID_C_friends).get_sub();

  for(const auto &friend_symb : friends)
  {
    const cpp_scopet &friend_scope =
      cpp_scopes.get_scope(friend_symb.get(ID_identifier));

    for(cpp_scopet *pscope = &(cpp_scopes.current_scope());
        !(pscope->is_root_scope());
        pscope = &(pscope->get_parent()))
    {
      if(friend_scope.identifier == pscope->identifier)
        return false; // ok

      // Check if this scope is an instantiation of the friend template.
      if(pscope->is_class())
      {
        // For template friend declarations, the friend scope points to
        // the template class (e.g., "tag-B"), while the current scope
        // is an instantiation (e.g., "tag-B<int>"). Check if the scope
        // identifier starts with the friend identifier followed by '<'.
        const std::string &friend_id = id2string(friend_scope.identifier);
        const std::string &scope_id = id2string(pscope->identifier);
        if(
          scope_id.size() > friend_id.size() &&
          scope_id.compare(0, friend_id.size(), friend_id) == 0 &&
          scope_id[friend_id.size()] == '<')
        {
          return false; // ok — instantiation of friend template
        }

        // C++11 (DR 45): nested classes have access to the enclosing
        // class's friends.
        if(config.cpp.cpp_standard >= configt::cppt::cpp_standardt::CPP11)
        {
          continue;
        }

        break;
      }
    }
  }

  return true; // not ok
}

void cpp_typecheckt::get_bases(
  const struct_typet &type,
  std::set<irep_idt> &set_bases) const
{
  for(const auto &b : type.bases())
  {
    DATA_INVARIANT(b.id() == ID_base, "base class expression expected");

    if(static_cast<const exprt &>(b).type().id() != ID_struct_tag)
      continue;
    const symbolt &base_sym = lookup(b.type());
    if(base_sym.type.id() != ID_struct)
      continue;
    const struct_typet &base = to_struct_type(base_sym.type);

    set_bases.insert(base.get(ID_name));
    get_bases(base, set_bases);
  }
}

void cpp_typecheckt::get_virtual_bases(
  const struct_typet &type,
  std::list<irep_idt> &vbases) const
{
  if(std::find(vbases.begin(), vbases.end(), type.get(ID_name)) != vbases.end())
    return;

  for(const auto &b : type.bases())
  {
    DATA_INVARIANT(b.id() == ID_base, "base class expression expected");

    if(static_cast<const exprt &>(b).type().id() != ID_struct_tag)
      continue;
    const symbolt &base_sym = lookup(b.type());
    if(base_sym.type.id() != ID_struct)
      continue;
    const struct_typet &base = to_struct_type(base_sym.type);

    if(b.get_bool(ID_virtual))
      vbases.push_back(base.get(ID_name));

    get_virtual_bases(base, vbases);
  }
}

bool cpp_typecheckt::subtype_typecast(
  const struct_typet &from,
  const struct_typet &to) const
{
  if(from.get(ID_name) == to.get(ID_name))
    return true;

  std::set<irep_idt> bases;

  get_bases(from, bases);

  return bases.find(to.get(ID_name)) != bases.end();
}

bool cpp_typecheckt::base_publicly_accessible(
  const struct_typet &from,
  const struct_typet &to) const
{
  if(from.get(ID_name) == to.get(ID_name))
    return true;

  if(disable_access_control)
    return true;

  // Check if we're inside the derived class or any of its bases — if so,
  // all bases are accessible regardless of access specifier.
  const irep_idt &from_name = from.get(ID_name);
  for(cpp_scopet *scope = cpp_scopes.current_scope_ptr; !scope->is_root_scope();
      scope = &scope->get_parent())
  {
    if(scope->is_class())
    {
      if(scope->identifier == from_name)
        return true;
      // Also allow if from derives from the scope class (e.g., when
      // resolving a qualified name like ::Base::method() from within
      // a derived class member function).
      if(subtype_typecast(from, to_struct_type(lookup(scope->identifier).type)))
        return true;
    }
  }

  // Walk the inheritance chain checking that all bases are public.
  for(const auto &b : from.bases())
  {
    if(b.type().id() != ID_struct_tag)
      continue;

    const struct_typet &base_struct = follow_tag(to_struct_tag_type(b.type()));

    if(base_struct.get(ID_name) == to.get(ID_name))
      return b.get(ID_access) == ID_public;

    if(base_publicly_accessible(base_struct, to))
      return b.get(ID_access) == ID_public;
  }

  return false;
}

void cpp_typecheckt::make_ptr_typecast(
  exprt &expr,
  const pointer_typet &dest_type)
{
  typet src_type = expr.type();

  PRECONDITION(src_type.id() == ID_pointer);

  const struct_typet &src_struct =
    follow_tag(to_struct_tag_type(to_pointer_type(src_type).base_type()));

  const struct_typet &dest_struct =
    follow_tag(to_struct_tag_type(dest_type.base_type()));

  PRECONDITION(
    subtype_typecast(src_struct, dest_struct) ||
    subtype_typecast(dest_struct, src_struct));

  // For upcasts (derived* -> base*) and downcasts (base* -> derived*),
  // adjust the pointer offset when the base class is not the first base
  // (i.e., its members don't start at offset 0 in the derived class's
  // flat struct layout).
  const struct_typet *derived = nullptr;
  const struct_typet *base = nullptr;
  bool is_upcast = false;
  if(subtype_typecast(src_struct, dest_struct))
  {
    derived = &src_struct;
    base = &dest_struct;
    is_upcast = true;
  }
  else
  {
    derived = &dest_struct;
    base = &src_struct;
    is_upcast = false;
  }

  {
    const irep_idt &base_name = base->get(ID_name);

    // Skip offset adjustment for virtual inheritance — the layout
    // involves virtual base pointers that member_offset cannot handle.
    std::list<irep_idt> virtual_bases;
    get_virtual_bases(*derived, virtual_bases);
    if(!virtual_bases.empty())
    {
      expr = typecast_exprt(expr, dest_type);
      return;
    }

    // Walk the inheritance chain from derived to base. At each level,
    // check if the target base is reachable through the first direct
    // base. If not, compute the offset of the non-first base's first
    // component.
    bool needs_offset = false;
    const struct_typet *current = derived;
    irep_idt offset_base_name;
    while(current->get(ID_name) != base_name)
    {
      const auto &bases = current->bases();
      if(bases.empty())
        break;

      const struct_typet &first_base =
        to_struct_type(lookup(bases.front().type()).type);
      std::set<irep_idt> first_base_set;
      first_base_set.insert(first_base.get(ID_name));
      get_bases(first_base, first_base_set);

      if(
        first_base.get(ID_name) == base_name || first_base_set.count(base_name))
      {
        current = &first_base;
        continue;
      }

      // base is reachable through a non-first base.
      for(std::size_t i = 1; i < bases.size(); ++i)
      {
        const struct_typet &nth_base =
          to_struct_type(lookup(bases[i].type()).type);
        std::set<irep_idt> nth_base_set;
        nth_base_set.insert(nth_base.get(ID_name));
        get_bases(nth_base, nth_base_set);

        if(nth_base.get(ID_name) == base_name || nth_base_set.count(base_name))
        {
          offset_base_name = nth_base.get(ID_name);
          needs_offset = true;
          break;
        }
      }
      break;
    }

    if(needs_offset)
    {
      // Find the first component of the non-first base in derived.
      const std::string bn = id2string(offset_base_name);
      std::string base_prefix;
      if(bn.size() > 4 && bn.substr(0, 4) == "tag-")
        base_prefix = bn.substr(4) + "::";
      else
        base_prefix = bn + "::";
      const std::string tag_prefix = bn + "::";

      for(const auto &comp : derived->components())
      {
        const std::string cn = id2string(comp.get_name());
        if(
          (cn.size() > base_prefix.size() &&
           cn.compare(0, base_prefix.size(), base_prefix) == 0) ||
          (cn.size() > tag_prefix.size() &&
           cn.compare(0, tag_prefix.size(), tag_prefix) == 0))
        {
          auto offset = member_offset(*derived, comp.get_name(), *this);
          if(offset.has_value() && *offset != 0)
          {
            exprt char_ptr =
              typecast_exprt(expr, pointer_type(unsigned_char_type()));
            exprt offset_expr =
              from_integer(is_upcast ? *offset : -*offset, pointer_diff_type());
            exprt adjusted = plus_exprt(char_ptr, offset_expr);
            expr = typecast_exprt(adjusted, dest_type);
            return;
          }
          break;
        }
      }
    }
  }

  expr = typecast_exprt(expr, dest_type);
}
