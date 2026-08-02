/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/find_symbols.h>
#include <util/mathematical_expr.h>
#include <util/pointer_expr.h>
#include <util/source_location.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

#include <ansi-c/builtin_factory.h>
#include <ansi-c/gcc_version.h>

#include "cpp_declarator.h"
#include "cpp_sfinae_context.h"
#include "cpp_util.h"
#include "expr2cpp.h"

cpp_typecheckt::cpp_typecheckt(
  cpp_parse_treet &_cpp_parse_tree,
  symbol_table_baset &_symbol_table,
  const std::string &_module,
  message_handlert &message_handler)
  : c_typecheck_baset(_symbol_table, _module, message_handler),
    cpp_parse_tree(_cpp_parse_tree),
    template_counter(0),
    anon_counter(0),
    disable_access_control(false),
    support_float16_type(false)
{
  if(config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::GCC)
  {
    gcc_versiont gcc_version;
    gcc_version.get("gcc");
    if(
      gcc_version.flavor == gcc_versiont::flavort::GCC &&
      gcc_version.is_at_least(13u))
    {
      support_float16_type = true;
    }
  }
}

cpp_typecheckt::cpp_typecheckt(
  cpp_parse_treet &_cpp_parse_tree,
  symbol_table_baset &_symbol_table1,
  const symbol_table_baset &_symbol_table2,
  const std::string &_module,
  message_handlert &message_handler)
  : c_typecheck_baset(_symbol_table1, _symbol_table2, _module, message_handler),
    cpp_parse_tree(_cpp_parse_tree),
    template_counter(0),
    anon_counter(0),
    disable_access_control(false),
    support_float16_type(false)
{
  if(config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::GCC)
  {
    gcc_versiont gcc_version;
    gcc_version.get("gcc");
    if(
      gcc_version.flavor == gcc_versiont::flavort::GCC &&
      gcc_version.is_at_least(13u))
    {
      support_float16_type = true;
    }
  }
}

void cpp_typecheckt::convert(cpp_itemt &item)
{
  if(item.is_declaration())
    convert(to_cpp_declaration(item));
  else if(item.is_linkage_spec())
    convert(item.get_linkage_spec());
  else if(item.is_namespace_spec())
    convert(item.get_namespace_spec());
  else if(item.is_using())
    convert(item.get_using());
  else if(item.is_static_assert())
    convert(item.get_static_assert());
  else
  {
    error().source_location = item.source_location();
    error() << "unknown parse-tree element: " << item.id() << eom;
    throw 0;
  }
}

/// typechecking main method
void cpp_typecheckt::typecheck()
{
  // Clear static caches from previous translation units to avoid
  // dangling scope pointers when type-checking multiple files.
  cpp_scopet::clear_static_caches();

  // default linkage is "automatic"
  current_linkage_spec = ID_auto;

  for(auto &item : cpp_parse_tree.items)
  {
    const auto &loc = item.source_location();
    const std::string file = id2string(loc.get_file());
    bool is_system =
      file.find("/usr/include/") == 0 || file.find("/usr/lib/") == 0;

    if(is_system)
    {
      // System-header item: analogous to SFINAE — a failure to
      // type-check an item from a system header (typically a
      // built-in or implementation-defined construct we don't
      // model) should not be a compilation error against user code.
      // Suppress diagnostics and roll the error count back.
      try
      {
        sfinae_contextt sfinae_guard{*this};
        convert(item);
      }
      catch(...)
      {
      }
    }
    else
    {
      try
      {
        convert(item);
      }
      catch(int)
      {
      }
    }
  }

  // If errors occurred during the convert loop but we still have
  // declarations to process, the error count may have been
  // incremented. We don't re-throw here; errors will be detected
  // by typecheck_main via the error count.

  // Fold __safe_multiply::__c before static initialization.
  // __c = uintmax_t(1) << (sizeof(intmax_t) * 4) = 2^32 on 64-bit.
  // CBMC's constexpr evaluation may fail for this shift inside
  // template classes on older GCC, causing division-by-zero in <ratio>.
  for(auto &entry : symbol_table.symbols)
  {
    symbolt &sym = symbol_table.get_writeable_ref(entry.first);
    if(
      id2string(sym.base_name) == "__c" &&
      id2string(sym.name).find("__safe_multiply") != std::string::npos)
    {
      typet t = sym.type;
      t.remove(ID_C_constant);
      sym.value = from_integer(mp_integer(1) << 32, t);
      sym.is_macro = true;
    }
  }

  static_and_dynamic_initialization();

  // Provide models for constexpr functions that are evaluated during
  // method body type-checking. These must be set before
  // typecheck_method_bodies() so that constexpr evaluation uses our
  // models instead of producing nondet values.
  //
  // Wrap the constant in a `code_block { return true; }` rather than
  // assigning a bare `true_exprt()` to `sym.value`.  The latter form
  // makes `convert_function` reject the symbol with
  //   function 'X' is initialized with constant
  // when the symbol is later visited by `typecheck_method_bodies`.
  // The block-with-return form is what `provide_stdlib_bodies` uses
  // for the same override at `do_not_typechecked` time, and it is
  // semantically equivalent for the constexpr-eval consumer
  // (`typecheck_side_effect_function_call` recognises
  // `code_block { return <const> }` and uses the constant).
  for(auto &entry : symbol_table.symbols)
  {
    symbolt &sym = symbol_table.get_writeable_ref(entry.first);
    const std::string name = id2string(sym.name);
    const std::string base = id2string(sym.base_name);
    if(
      (base == "_S_nothrow_relocate" || base == "_S_use_relocate") &&
      name.find("vector") != std::string::npos && sym.is_macro)
    {
      code_blockt block;
      block.add(code_frontend_returnt(true_exprt()));
      sym.value = std::move(block);
      sym.value.type() = sym.type;
    }
  }

  typecheck_method_bodies();

  typecheck_contracts();

  do_not_typechecked();

  // do_not_typechecked() elaborates implicitly-defined / explicitly-defaulted
  // special members (e.g. copy constructors) that were not odr-used until now.
  // Their memberwise base/member initializers odr-use the corresponding
  // base/member constructors ([class.copy.ctor]/14), which may themselves
  // still be deferred template-instance bodies.  Those odr-uses are recorded
  // in odr_used_by_member_initializer; re-run the deferred-body drain (which
  // honours that set) to elaborate them, and re-run do_not_typechecked() in
  // case the freshly elaborated bodies odr-use further implicit members.
  // Iterate to a fixpoint ([temp.inst]/4).
  while(!deferred_method_bodies.empty())
  {
    const std::size_t before = deferred_method_bodies.size();
    typecheck_method_bodies();
    do_not_typechecked();
    if(deferred_method_bodies.size() == before)
      break;
  }

  // A function-template instance can be left HALF-converted: its eager
  // conversion (required for `auto` return-type deduction,
  // [dcl.spec.auto]/11) ran nested inside overload-candidate matching
  // and was absorbed by the SFINAE machinery -- leaving a raw body, an
  // undeduced return type, and a methods_seen entry that blocks
  // re-queueing (std::forward<int&> instantiated from
  // _Function_handler::_M_invoke).  Calls were built against the
  // half-symbol, so at goto conversion it is a bodyless callee and the
  // std::function invocation havocs.  [temp.inst]/4: the odr-used
  // specialization must be instantiated; finish such conversions here,
  // to a fixpoint (a retry can instantiate further templates).
  for(std::size_t rounds = 0; rounds < 5; ++rounds)
  {
    std::vector<irep_idt> to_finish;
    for(const auto &entry : symbol_table)
    {
      const symbolt &sym = entry.second;
      // Restricted to bodies from SYSTEM HEADERS: the half-converted
      // state arises from stdlib instances (std::forward et al.)
      // whose eager conversion ran under candidate matching; bodies
      // converted through paths that do not stamp #cpp_converted
      // (e.g. nested lambdas) must not be re-converted.
      const std::string sym_file = id2string(sym.location.get_file());
      const bool system_header = sym_file.find("/usr/include/") == 0 ||
                                 sym_file.find("/usr/lib/") == 0 ||
                                 sym_file.find("/Applications/") == 0;
      if(
        system_header && sym.type.id() == ID_code &&
        sym.value.id() == ID_code && sym.mode == ID_cpp &&
        !sym.value.get_bool("#cpp_converted") && !sym.is_type &&
        functions_being_typechecked.count(sym.name) == 0 &&
        deferred_method_bodies.find(sym.name) == deferred_method_bodies.end())
      {
        to_finish.push_back(entry.first);
      }
    }
    if(to_finish.empty())
      break;
    for(const auto &id : to_finish)
    {
      symbolt &sym = symbol_table.get_writeable_ref(id);
      try
      {
        convert_function(sym);
      }
      catch(...)
      {
        // cannot be completed: leave it; goto conversion will
        // diagnose the call sites
      }
    }
    typecheck_method_bodies();
  }

  provide_stdlib_bodies();

  clean_up();

  // Ensure all type symbols referenced in the symbol table exist.
  // System header processing may fail partway through template
  // instantiation (caught by catch(...) in linkage spec processing),
  // leaving struct_tag_typet references to symbols that were never
  // created. Create incomplete stubs for any missing type symbols
  // so that goto program validation does not crash.
  {
    find_symbols_sett referenced;
    for(const auto &entry : symbol_table.symbols)
    {
      find_type_and_expr_symbols(entry.second.type, referenced);
      if(entry.second.value.is_not_nil())
        find_type_and_expr_symbols(entry.second.value, referenced);
    }
    for(const auto &id : referenced)
    {
      if(!symbol_table.has_symbol(id))
      {
        const std::string id_str = id2string(id);
        // Create stubs for missing tag types (struct/union/enum).
        // These arise from failed template instantiations in system
        // headers. The struct_tag_typet reference remains in other
        // types but the type symbol was never created.
        if(id_str.find("tag-") != std::string::npos)
        {
          type_symbolt stub{id, struct_typet(), ID_cpp};
          to_struct_type(stub.type).make_incomplete();
          symbol_table.insert(std::move(stub));
        }
      }
    }
  }
}

const struct_typet &cpp_typecheckt::this_struct_type()
{
  const exprt &this_expr = cpp_scopes.current_scope().this_expr;

  CHECK_RETURN(this_expr.is_not_nil());
  CHECK_RETURN(this_expr.type().id() == ID_pointer);

  const typet &t = to_pointer_type(this_expr.type()).base_type();
  CHECK_RETURN(t.id() == ID_struct_tag);
  return follow_tag(to_struct_tag_type(t));
}

std::string cpp_typecheckt::to_string(const exprt &expr)
{
  return expr2cpp(expr, *this);
}

std::string cpp_typecheckt::to_string(const typet &type)
{
  return type2cpp(type, *this);
}

bool cpp_typecheckt::empty_brace_value_initializes_scalar() const
{
  // C++ [dcl.init.list]/3.10: an empty braced-init-list `{}` for a
  // scalar performs value-initialization, yielding the scalar's
  // zero value.  This is a C++11 feature; CBMC accepts it in all
  // C++ modes for consistency with other permissive extensions.
  return true;
}

void cpp_typecheckt::typecheck_contracts()
{
  // Collect symbols to process (avoid modifying symbol table while iterating)
  std::vector<irep_idt> symbols_with_contracts;
  for(const auto &entry : symbol_table.symbols)
  {
    if(
      entry.second.type.id() == ID_code &&
      to_code_with_contract_type(entry.second.type).has_contract())
    {
      symbols_with_contracts.push_back(entry.first);
    }
  }

  for(const auto &id : symbols_with_contracts)
  {
    symbolt &symbol = symbol_table.get_writeable_ref(id);
    code_with_contract_typet code_type =
      to_code_with_contract_type(symbol.type);

    // Enter the function's scope so that parameter names resolve
    cpp_save_scopet saved_scope(cpp_scopes);
    cpp_scopes.set_scope(symbol.name);

    binding_exprt::variablest parameter_symbols;

    const auto &return_type = code_type.return_type();
    bool added_return_value = false;
    if(return_type.id() != ID_empty)
    {
      parameter_symbols.emplace_back(
        CPROVER_PREFIX "return_value", return_type);

      // Add __CPROVER_return_value to the symbol table and scope
      // so that type-checking of ensures clauses can resolve it.
      symbolt rv_symbol{};
      rv_symbol.name = CPROVER_PREFIX "return_value";
      rv_symbol.base_name = CPROVER_PREFIX "return_value";
      rv_symbol.type = return_type;
      rv_symbol.mode = symbol.mode;
      rv_symbol.is_lvalue = true;
      auto result = symbol_table.insert(std::move(rv_symbol));
      if(result.second)
      {
        added_return_value = true;
        cpp_scopes.put_into_scope(result.first);
      }
    }

    for(const auto &p : code_type.parameters())
    {
      if(!p.get_identifier().empty())
        parameter_symbols.emplace_back(p.get_identifier(), p.type());
    }

    for(auto &req : code_type.c_requires())
    {
      typecheck_expr(req);
      implicit_typecast_bool(req);
      lambda_exprt lambda{parameter_symbols, req};
      lambda.add_source_location() = req.source_location();
      req.swap(lambda);
    }

    for(auto &ens : code_type.c_ensures())
    {
      typecheck_expr(ens);
      implicit_typecast_bool(ens);
      lambda_exprt lambda{parameter_symbols, ens};
      lambda.add_source_location() = ens.source_location();
      ens.swap(lambda);
    }

    // Create a dedicated contract symbol
    symbolt contract_sym;
    contract_sym.name = "contract::" + id2string(symbol.name);
    contract_sym.base_name = symbol.base_name;
    contract_sym.pretty_name = symbol.pretty_name;
    contract_sym.is_property = true;
    contract_sym.type = code_type;
    contract_sym.mode = symbol.mode;
    contract_sym.module = module;
    contract_sym.location = symbol.location;

    symbol_table.insert(std::move(contract_sym));

    // Remove contracts from the original symbol
    symbol.type.remove(ID_C_spec_requires);
    symbol.type.remove(ID_C_spec_ensures);
    symbol.type.remove(ID_C_spec_assigns);
    symbol.type.remove(ID_C_spec_frees);

    // Clean up temporary __CPROVER_return_value symbol
    if(added_return_value)
      symbol_table.remove(CPROVER_PREFIX "return_value");
  }
}

bool cpp_typecheck(
  cpp_parse_treet &cpp_parse_tree,
  symbol_table_baset &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  cpp_typecheckt cpp_typecheck(
    cpp_parse_tree, symbol_table, module, message_handler);
  return cpp_typecheck.typecheck_main();
}

bool cpp_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns)
{
  const unsigned errors_before =
    message_handler.get_message_count(messaget::M_ERROR);

  symbol_tablet symbol_table;
  cpp_parse_treet cpp_parse_tree;

  cpp_typecheckt cpp_typecheck(
    cpp_parse_tree, symbol_table, ns.get_symbol_table(), "", message_handler);

  try
  {
    cpp_typecheck.typecheck_expr(expr);
  }

  catch(int)
  {
    cpp_typecheck.error();
  }

  catch(const char *e)
  {
    cpp_typecheck.error() << e << messaget::eom;
  }

  catch(const std::string &e)
  {
    cpp_typecheck.error() << e << messaget::eom;
  }

  catch(const invalid_source_file_exceptiont &e)
  {
    cpp_typecheck.error().source_location = e.get_source_location();
    cpp_typecheck.error() << e.get_reason() << messaget::eom;
  }

  return message_handler.get_message_count(messaget::M_ERROR) != errors_before;
}

/// Initialization of static objects:
///
/// "Objects with static storage duration (3.7.1) shall be zero-initialized
/// (8.5) before any other initialization takes place. Zero-initialization
/// and initialization with a constant expression are collectively called
/// static initialization; all other initialization is dynamic
/// initialization. Objects of POD types (3.9) with static storage duration
/// initialized with constant expressions (5.19) shall be initialized before
/// any dynamic initialization takes place. Objects with static storage
/// duration defined in namespace scope in the same translation unit and
/// dynamically initialized shall be initialized in the order in which their
/// definition appears in the translation unit. [Note: 8.5.1 describes the
/// order in which aggregate members are initialized. The initialization
/// of local static objects is described in 6.7. ]"
void cpp_typecheckt::static_and_dynamic_initialization()
{
  code_blockt init_block; // Dynamic Initialization Block

  disable_access_control = true;

  for(const irep_idt &d_it : dynamic_initializations)
  {
    symbolt &symbol = symbol_table.get_writeable_ref(d_it);

    if(symbol.is_extern)
      continue;

    // PODs with constant initializers are statically initialized.
    // PODs with non-constant initializers (e.g., function calls)
    // need dynamic initialization in declaration order.
    if(cpp_is_pod(symbol.type))
    {
      // Check if the initializer contains side effects (function
      // calls, etc.) that require dynamic initialization.
      bool has_side_effect = false;
      if(symbol.value.is_not_nil())
      {
        symbol.value.visit_pre(
          [&has_side_effect](const exprt &e)
          {
            if(e.id() == ID_side_effect)
              has_side_effect = true;
          });
      }

      // N5008 [class.default.ctor]/3 + [basic.start.static]: a class with a
      // default member initializer (NSDMI) has a non-trivial default
      // constructor.  A value-less namespace-scope definition (`Q g;` for
      // `struct Q { int t = 5; };`, or an enclosing class that has such a
      // class as a member/array element) must run that constructor so the
      // NSDMI is applied; merely zero-initializing it (the effect of skipping
      // it here) would leave the member at 0 instead of its declared default.
      // Route such a definition to the default-constructor path below.
      // Members with an explicit initializer are unaffected (the initializer
      // overrides the NSDMI, [class.base.init]/9).
      const bool needs_default_ctor =
        symbol.value.is_nil() && has_default_member_initializer(symbol.type);

      if(!has_side_effect && !needs_default_ctor)
        continue;
    }

    DATA_INVARIANT(symbol.is_static_lifetime, "should be static");
    DATA_INVARIANT(!symbol.is_type, "should not be a type");
    DATA_INVARIANT(symbol.type.id() != ID_code, "should not be code");

    exprt symbol_expr = cpp_symbol_expr(symbol);

    // initializer given?
    if(symbol.value.is_not_nil())
    {
      if(symbol.value.id() == ID_code)
      {
        // This will be a constructor call,
        // which we execute.
        init_block.add(to_code(symbol.value));
      }
      else
      {
        // POD with non-constant initializer: create assignment
        init_block.add(code_frontend_assignt(symbol_expr, symbol.value));
      }

      // Make it nil to get zero initialization by
      // __CPROVER_initialize
      symbol.value.make_nil();
    }
    else
    {
      // use default constructor
      exprt::operandst ops;

      auto call = cpp_constructor(symbol.location, symbol_expr, ops);

      if(call.has_value())
        init_block.add(call.value());
    }
  }

  dynamic_initializations.clear();

  // Create the dynamic initialization procedure
  symbolt init_symbol{
    "#cpp_dynamic_initialization#" + id2string(module),
    code_typet({}, typet(ID_constructor)),
    ID_cpp};
  init_symbol.base_name = "#cpp_dynamic_initialization#" + id2string(module);
  init_symbol.value.swap(init_block);
  init_symbol.module = module;

  symbol_table.insert(std::move(init_symbol));

  disable_access_control = false;
}

void cpp_typecheckt::do_not_typechecked()
{
  bool cont;

  do
  {
    cont = false;

    for(auto it = symbol_table.begin(); it != symbol_table.end(); ++it)
    {
      const symbolt &symbol = it->second;

      if(
        symbol.value.id() == ID_cpp_not_typechecked &&
        symbol.value.get_bool(ID_is_used))
      {
        DATA_INVARIANT(symbol.type.id() == ID_code, "must be code");
        exprt value = symbol.value;

        if(symbol.base_name == "operator=")
        {
          cpp_declaratort declarator;
          declarator.add_source_location() = symbol.location;
          default_assignop_value(
            lookup(symbol.type.get(ID_C_member_name)), declarator);
          value.swap(declarator.value());
          cont = true;
        }
        else if(symbol.value.operands().size() == 1)
        {
          value = to_unary_expr(symbol.value).op();
          cont = true;
        }
        else
          UNREACHABLE; // Don't know what to do!

        symbolt &writable_symbol = it.get_writeable_symbol();
        writable_symbol.value.swap(value);
        convert_function(writable_symbol);
      }
    }
  } while(cont);

  for(auto it = symbol_table.begin(); it != symbol_table.end(); ++it)
  {
    if(it->second.value.id() == ID_cpp_not_typechecked)
      it.get_writeable_symbol().value.make_nil();
  }
}

void cpp_typecheckt::clean_up()
{
  auto it = symbol_table.begin();

  while(it != symbol_table.end())
  {
    auto cur_it = it;
    it++;

    const symbolt &symbol = cur_it->second;

    // erase templates and all member functions that have not been converted
    if(symbol.type.get_bool(ID_is_template))
    {
      symbol_table.erase(cur_it);
      continue;
    }
    else if(symbol.type.id() == ID_code)
    {
      // N5008 [dcl.fct]/5 + [basic.scope.param]: a parameter's name is
      // local to its function.  A member of a class template instance
      // that was never odr-used keeps its PARSE-level parameter names
      // ("_m") in its function type; goto conversion would then
      // materialise stub parameter symbols under those bare names,
      // which collide across instantiations (my_template<int>::set and
      // my_template<unsigned char>::set both claiming "_m", tripping
      // the goto-model parameter-type validation).  Qualify them with
      // the function's own name, as convert_parameter does for
      // converted bodies.
      code_typet &code_type = to_code_type(cur_it.get_writeable_symbol().type);
      for(auto &parameter : code_type.parameters())
      {
        const irep_idt &id = parameter.get_identifier();
        if(
          !id.empty() && id2string(id).find("::") == std::string::npos &&
          !symbol_table.has_symbol(id))
        {
          parameter.set_identifier(
            id2string(symbol.name) + "::" + id2string(id));
        }
      }
      if(deferred_typechecking.find(symbol.name) != deferred_typechecking.end())
      {
        symbol_table.get_writeable_ref(symbol.name).value.make_nil();
      }
      continue;
    }
    else if(
      deferred_typechecking.find(symbol.name) != deferred_typechecking.end())
    {
      // Member functions in template scopes that were never instantiated.
      // Clear the un-typechecked body but keep the symbol so that
      // goto conversion can create a no-body stub if it's referenced.
      symbol_table.get_writeable_ref(symbol.name).value.make_nil();
      continue;
    }
    else if(symbol.type.id() == ID_struct || symbol.type.id() == ID_union)
    {
      // remove methods from 'components'
      struct_union_typet &struct_union_type =
        to_struct_union_type(cur_it.get_writeable_symbol().type);

      const struct_union_typet::componentst &components =
        struct_union_type.components();

      struct_union_typet::componentst data_members;
      data_members.reserve(components.size());

      struct_union_typet::componentst &function_members =
        (struct_union_typet::componentst &)(struct_union_type.add(ID_methods)
                                              .get_sub());

      function_members.reserve(components.size());

      for(const auto &compo_it : components)
      {
        if(compo_it.get_bool(ID_is_static) || compo_it.get_bool(ID_is_type))
        {
          // skip it
        }
        else if(compo_it.type().id() == ID_code)
        {
          function_members.push_back(compo_it);
        }
        else
        {
          data_members.push_back(compo_it);
        }
      }

      struct_union_type.components().swap(data_members);
    }
  }
}

bool cpp_typecheckt::builtin_factory(const irep_idt &identifier)
{
  return ::builtin_factory(
    identifier, support_float16_type, symbol_table, get_message_handler());
}

bool cpp_typecheckt::contains_cpp_name(const exprt &expr)
{
  if(expr.id() == ID_cpp_name || expr.id() == ID_cpp_declaration)
    return true;

  for(const exprt &op : expr.operands())
  {
    if(contains_cpp_name(op))
      return true;
  }
  return false;
}
