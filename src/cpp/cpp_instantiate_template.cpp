/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck.h"

#ifdef DEBUG
#include <iostream>
#endif

#include <util/arith_tools.h>
#include <util/base_exceptions.h> // IWYU pragma: keep
#include <util/c_types.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

#include "cpp_convert_type.h"
#include "cpp_sfinae_context.h"
#include "cpp_template_qualifiers.h"
#include "cpp_type2name.h"
#include "cpp_typecheck_resolve.h"

#include <algorithm>

namespace
{
cpp_scopet *id_map_lookup(cpp_scopest &scopes, const irep_idt &key)
{
  auto it = scopes.id_map.find(key);
  return it != scopes.id_map.end() ? static_cast<cpp_scopet *>(it->second)
                                   : nullptr;
}
} // namespace

std::string cpp_typecheckt::template_suffix(
  const cpp_template_args_tct &template_args)
{
  // quick hack
  std::string result="<";
  bool first=true;

  const cpp_template_args_tct::argumentst &arguments=
    template_args.arguments();

  for(const auto &expr : arguments)
  {
    if(first)
      first=false;
    else
      result+=',';

    DATA_INVARIANT(
      expr.id() != ID_ambiguous, "template argument must not be ambiguous");

    if(expr.id()==ID_type)
    {
      const typet &type=expr.type();
      if(type.id() == ID_struct_tag || type.id() == ID_union_tag)
      {
        // Include cv-qualifiers so that T and const T are distinct
        // instantiations (e.g., forward<const X> vs forward<X>).
        if(type.get_bool(ID_C_constant))
          result += "const ";
        if(type.get_bool(ID_C_volatile))
          result += "volatile ";
        result += id2string(to_tag_type(type).get_identifier());
      }
      else
        result+=cpp_type2name(type);
    }
    else // expression
    {
      exprt e=expr;

      // Recursively resolve constant symbols to their values, so that
      // expressions like "1000000000000000000l * ::value" can be evaluated.
      // Multiple passes may be needed for chains of symbol references.
      for(int pass = 0; pass < 10; ++pass)
      {
        bool changed = false;
        e.visit_pre(
          [this, &changed](exprt &node)
          {
            if(node.id() == ID_symbol)
            {
              const symbolt &symbol = lookup(to_symbol_expr(node).identifier());
              if(symbol.value.is_not_nil() && cpp_is_pod(symbol.type))
              {
                node = symbol.value;
                changed = true;
              }
            }
          });
        if(!changed)
          break;
        simplify(e, *this);
        if(e.is_constant())
          break;
      }

      // If a template's default non-type argument failed to
      // resolve (e.g. a reference-template-parameter whose default
      // names a member that doesn't exist on the actual template
      // argument type — like libstdc++-wrapping code using
      //   template<typename T, const T &empty = T::blank>
      // with T = std::basic_string, which has no `blank`), `e` is
      // nil.  Rather than fail with `expected constant expression,
      // but got '<<expr:nil>>'`, emit a placeholder suffix so the
      // instantiation can proceed (with an undefined value).  This
      // matches the "soft failure" behaviour of other template
      // argument fallbacks in this file.
      if(e.is_nil())
      {
        result += "<nil_default>";
        continue;
      }

      make_constant(e);

      // this must be a constant, which includes true/false
      mp_integer i;

      if(e == true)
        i=1;
      else if(e == false)
        i=0;
      else
      {
        // follow c_enum_tag to c_enum for to_integer
        if(e.type().id() == ID_c_enum_tag)
          e.type() = follow_tag(to_c_enum_tag_type(e.type()));

        if(to_integer(to_constant_expr(e), i))
        {
          // C++20: floating-point non-type template parameters
          if(
            e.is_constant() &&
            (e.type().id() == ID_floatbv || e.type().id() == ID_fixedbv ||
             e.type().id() == ID_double || e.type().id() == ID_float))
          {
            result += id2string(to_constant_expr(e).get_value());
          }
          else
          {
            error().source_location = expr.find_source_location();
            error() << "template argument expression expected to be "
                    << "scalar constant, but got '" << to_string(e) << "'"
                    << eom;
            throw 0;
          }
        }
        else
        {
          result += integer2string(i);
        }
      }
    }
  }

  result+='>';

  return result;
}

void cpp_typecheckt::show_instantiation_stack(std::ostream &out)
{
  for(const auto &e : instantiation_stack)
  {
    const symbolt &symbol = lookup(e.identifier);
    out << "instantiating '" << symbol.pretty_name << "' with <";

    forall_expr(a_it, e.full_template_args.arguments())
    {
      if(a_it != e.full_template_args.arguments().begin())
        out << ", ";

      if(a_it->id()==ID_type)
        out << to_string(a_it->type());
      else
        out << to_string(*a_it);
    }

    out << "> at " << e.source_location << '\n';
  }
}

/// Set up a scope as subscope of the template scope
cpp_scopet &cpp_typecheckt::sub_scope_for_instantiation(
  cpp_scopet &template_scope,
  const std::string &suffix)
{
  cpp_scopet::id_sett id_set =
    template_scope.lookup(suffix, cpp_scopet::SCOPE_ONLY);

  CHECK_RETURN(id_set.size() <= 1);

  if(id_set.size() == 1)
  {
    cpp_idt &cpp_id = **id_set.begin();
    CHECK_RETURN(cpp_id.is_template_scope());

    return static_cast<cpp_scopet &>(cpp_id);
  }
  else
  {
    cpp_scopet &sub_scope = template_scope.new_scope(suffix);
    sub_scope.id_class = cpp_idt::id_classt::TEMPLATE_SCOPE;
    sub_scope.prefix = template_scope.get_parent().prefix;
    sub_scope.suffix = suffix;
    sub_scope.add_using_scope(template_scope.get_parent());

    const std::string subscope_name =
      id2string(template_scope.identifier) + suffix;
    cpp_scopes.id_map.insert(
      cpp_scopest::id_mapt::value_type(subscope_name, &sub_scope));

    return sub_scope;
  }
}

/// Create or find the symbol for a class template instantiation.
///
/// Per [temp.inst]/1, class template specializations are implicitly
/// instantiated when referenced.  This function creates the incomplete
/// type symbol (marked with template_class_instance) that will be
/// elaborated later by elaborate_class_template.
///
/// When the symbol already exists (e.g., from a forward declaration in
/// libc++-20's __fwd/ headers), ensures that template metadata
/// (ID_C_template, ID_C_template_arguments) is set so that template
/// argument deduction ([temp.deduct.type]/3.3) can match instantiation
/// arguments.
const symbolt &cpp_typecheckt::class_template_symbol(
  const source_locationt &source_location,
  const symbolt &template_symbol,
  const cpp_template_args_tct &specialization_template_args,
  const cpp_template_args_tct &full_template_args)
{
  if(full_template_args.has_unassigned())
  {
    // Template arguments contain unresolved parameters (e.g., from a
    // template constructor like optional(const optional<_Up>&) where
    // _Up is the constructor's own template parameter). Create an
    // incomplete type symbol so that callers get a proper type symbol
    // (with "tag-" prefix) rather than the template declaration symbol.
    std::string suffix = template_suffix(full_template_args);

    cpp_scopet *template_scope =
      id_map_lookup(cpp_scopes, template_symbol.name);
    if(template_scope == nullptr)
      return template_symbol;

    irep_idt identifier = id2string(template_scope->get_parent().prefix) +
                          "tag-" + id2string(template_symbol.base_name) +
                          id2string(suffix);

    auto s_it = symbol_table.symbols.find(identifier);
    if(s_it != symbol_table.symbols.end())
      return s_it->second;

    const cpp_declarationt &template_decl =
      to_cpp_declaration(template_symbol.type);
    const bool is_union = template_decl.type().id() == ID_union;
    type_symbolt new_symbol{
      identifier,
      is_union ? static_cast<typet>(union_typet()) : struct_typet(),
      template_symbol.mode};
    new_symbol.base_name = template_symbol.base_name;
    new_symbol.location = template_symbol.location;
    to_struct_union_type(new_symbol.type).make_incomplete();

    symbolt *s_ptr;
    symbol_table.move(new_symbol, s_ptr);
    return *s_ptr;
  }

  // do we have args?
  if(full_template_args.arguments().empty())
  {
    // Empty args are valid for:
    // 1. Variadic templates with zero arguments (e.g., tuple<>)
    // 2. Explicit specializations with zero parameters
    const template_typet &template_type =
      to_cpp_declaration(template_symbol.type).template_type();
    const auto &params = template_type.template_parameters();
    bool valid_empty = params.empty();
    if(!valid_empty)
    {
      valid_empty = true;
      for(const auto &p : params)
      {
        if(!p.get_bool(ID_ellipsis))
        {
          valid_empty = false;
          break;
        }
      }
    }
    if(!valid_empty)
    {
      error().source_location = source_location;
      error() << "'" << template_symbol.base_name
              << "' is a template; thus, expected template arguments" << eom;
      throw 0;
    }
  }

  // produce new symbol name
  std::string suffix=template_suffix(full_template_args);

  cpp_scopet *template_scope = id_map_lookup(cpp_scopes, template_symbol.name);

  if(template_scope == nullptr)
  {
    error().source_location = source_location;
    error() << "template scope '" << template_symbol.base_name << "' not found"
            << eom;
    throw 0;
  }

  irep_idt identifier = id2string(template_scope->get_parent().prefix) +
                        "tag-" + id2string(template_symbol.base_name) +
                        id2string(suffix);

  // already there?
  symbol_table_baset::symbolst::const_iterator s_it =
    symbol_table.symbols.find(identifier);
  if(s_it != symbol_table.symbols.end())
  {
    // The symbol may have been created by a forward declaration
    // (e.g., libc++-20's __fwd/ headers) without template metadata.
    // Set ID_C_template and ID_C_template_arguments so that template
    // argument deduction can match instantiation arguments later.
    if(symbolt *ws = symbol_table.get_writeable(identifier))
    {
      if(ws->type.find(ID_C_template).is_nil())
      {
        ws->type.set(
          ID_C_template,
          to_cpp_declaration(template_symbol.type).template_type());
        ws->type.set(ID_C_template_arguments, specialization_template_args);
      }
    }
    return s_it->second;
  }

  // Create as incomplete struct/union, but mark as
  // "template_class_instance", to be elaborated later.
  const cpp_declarationt &template_decl =
    to_cpp_declaration(template_symbol.type);
  const bool is_union = template_decl.type().id() == ID_union;
  type_symbolt new_symbol{
    identifier,
    is_union ? static_cast<typet>(union_typet()) : struct_typet(),
    template_symbol.mode};
  new_symbol.pretty_name=template_symbol.pretty_name;
  new_symbol.location=template_symbol.location;
  to_struct_union_type(new_symbol.type).make_incomplete();
  new_symbol.type.set(ID_tag, template_symbol.type.find(ID_tag));
  if(template_symbol.type.get_bool(ID_C_class))
    new_symbol.type.set(ID_C_class, true);
  new_symbol.type.set(ID_template_class_instance, true);
  new_symbol.type.add_source_location()=template_symbol.location;
  new_symbol.type.set(
    ID_specialization_template_args, specialization_template_args);
  new_symbol.type.set(ID_full_template_args, full_template_args);
  new_symbol.type.set(ID_identifier, template_symbol.name);
  new_symbol.base_name=template_symbol.base_name;

  symbolt *s_ptr;
  symbol_table.move(new_symbol, s_ptr);

  // put into template scope
  cpp_idt &id=cpp_scopes.put_into_scope(*s_ptr, *template_scope);

  id.id_class=cpp_idt::id_classt::CLASS;
  id.is_scope=true;
  id.prefix = template_scope->get_parent().prefix +
              id2string(s_ptr->base_name) + id2string(suffix) + "::";
  id.class_identifier=s_ptr->name;
  id.id_class=cpp_idt::id_classt::CLASS;

  return *s_ptr;
}

/// Elaborate (instantiate) a class template instance.
///
/// Implements [temp.inst]/1: "Unless a class template specialization has been
/// explicitly instantiated or explicitly specialized, the class template
/// specialization is implicitly instantiated when the specialization is
/// referenced in a context that requires a completely-defined object type."
///
/// Also implements [temp.spec.partial.match]: when elaborating, searches
/// for the best-matching partial specialization using the rules from
/// [temp.spec.partial.order] and [temp.constr.order] (constraint ordering).

// Evaluate a constexpr function call with constant arguments.
// Returns the result as a constant expression, or nil if evaluation fails.
exprt try_evaluate_constexpr(
  const exprt &expr,
  const symbol_table_baset &symbol_table,
  const namespacet &ns)
{
  if(expr.id() != ID_side_effect)
    return nil_exprt();
  if(expr.get(ID_statement) != ID_function_call)
    return nil_exprt();

  const auto &call = to_side_effect_expr_function_call(expr);
  const auto &function = call.function();
  const auto &arguments = call.arguments();

  // All arguments must be constants (or address_of for reference
  // parameters, possibly wrapping a temporary with a constant value).
  for(const auto &arg : arguments)
  {
    if(arg.is_constant())
      continue;
    if(arg.id() == ID_address_of)
    {
      const auto &obj = to_address_of_expr(arg).object();
      if(obj.is_constant())
        continue;
      if(
        obj.id() == ID_side_effect && obj.operands().size() == 1 &&
        obj.operands()[0].is_constant())
        continue;
    }
    return nil_exprt();
  }

  // Look up the function body
  if(function.id() != ID_symbol)
    return nil_exprt();
  const irep_idt &func_id = to_symbol_expr(function).get_identifier();
  const symbolt *func_sym = symbol_table.lookup(func_id);
  if(!func_sym || func_sym->value.is_nil())
    return nil_exprt();

  const auto &body = func_sym->value;
  if(body.id() != ID_code)
    return nil_exprt();
  // Guard against re-entrant evaluation
  static int eval_depth = 0;
  if(eval_depth > 10)
    return nil_exprt();
  ++eval_depth;
  struct depth_guardt
  {
    ~depth_guardt()
    {
      --eval_depth;
    }
  } dg;

  // Get parameter names
  const auto &func_type = to_code_type(func_sym->type);
  const auto &params = func_type.parameters();
  if(params.size() != arguments.size())
    return nil_exprt();

  // Build a variable map: parameter → constant value
  // For reference parameters, unwrap address_of and temporaries.
  std::map<irep_idt, exprt> vars;
  for(std::size_t i = 0; i < params.size(); ++i)
  {
    if(arguments[i].id() == ID_address_of)
    {
      const auto &obj = to_address_of_expr(arguments[i]).object();
      if(obj.is_constant())
        vars[params[i].get_identifier()] = obj;
      else if(
        obj.id() == ID_side_effect && obj.operands().size() == 1 &&
        obj.operands()[0].is_constant())
        vars[params[i].get_identifier()] = obj.operands()[0];
      else
        vars[params[i].get_identifier()] = arguments[i];
    }
    else
      vars[params[i].get_identifier()] = arguments[i];
  }

  // Mini-interpreter: execute the body with bounded iterations
  std::function<std::optional<exprt>(const codet &, int)> execute;
  std::function<exprt(const exprt &)> eval;

  eval = [&](const exprt &e) -> exprt
  {
    if(e.id() == ID_symbol)
    {
      auto it = vars.find(to_symbol_expr(e).get_identifier());
      if(it != vars.end())
        return it->second;
      return e;
    }
    // dereference(symbol) where symbol maps to a constant:
    // the parameter is a reference, unwrap the dereference.
    if(
      e.id() == ID_dereference && e.operands().size() == 1 &&
      e.operands()[0].id() == ID_symbol)
    {
      auto it = vars.find(to_symbol_expr(e.operands()[0]).get_identifier());
      if(it != vars.end() && it->second.is_constant())
        return it->second;
    }
    if(e.id() == ID_side_effect && e.get(ID_statement) == ID_function_call)
    {
      // Recursively evaluate nested function calls
      exprt evaluated = try_evaluate_constexpr(e, symbol_table, ns);
      if(evaluated.is_not_nil())
        return evaluated;
    }
    // Rebuild expression with evaluated operands
    exprt result = e;
    for(auto &op : result.operands())
      op = eval(op);
    // Try to simplify
    simplify(result, ns);
    return result;
  };

  execute = [&](const codet &code, int depth) -> std::optional<exprt>
  {
    if(depth > 100)
      return std::nullopt;

    if(code.get_statement() == ID_return)
    {
      if(code.operands().size() == 1)
        return eval(code.op0());
      return std::nullopt;
    }
    if(code.get_statement() == ID_block)
    {
      for(const auto &stmt : code.operands())
      {
        if(stmt.id() != ID_code)
          continue;
        auto r = execute(to_code(stmt), depth + 1);
        if(r.has_value())
          return r;
      }
      return std::nullopt;
    }
    if(code.get_statement() == ID_ifthenelse)
    {
      exprt cond = eval(code.op0());
      if(cond.is_true() && code.operands()[1].id() == ID_code)
        return execute(to_code(code.operands()[1]), depth + 1);
      if(
        cond.is_false() && code.operands().size() > 2 &&
        code.operands()[2].id() == ID_code)
        return execute(to_code(code.operands()[2]), depth + 1);
      if(cond.is_false())
        return std::nullopt;
      return std::nullopt; // can't evaluate condition
    }
    if(code.get_statement() == ID_while)
    {
      for(int iter = 0; iter < 64; ++iter)
      {
        exprt cond = eval(code.op0());
        if(cond.is_false())
          return std::nullopt; // loop done, no return
        if(!cond.is_true())
          return std::nullopt; // can't evaluate condition
        if(code.operands()[1].id() != ID_code)
          return std::nullopt;
        auto r = execute(to_code(code.operands()[1]), depth + 1);
        if(r.has_value())
          return r;
      }
      return std::nullopt; // too many iterations
    }
    if(code.get_statement() == ID_assign)
    {
      const auto &lhs = code.op0();
      exprt rhs = eval(code.op1());
      if(lhs.id() == ID_symbol)
        vars[to_symbol_expr(lhs).get_identifier()] = rhs;
      return std::nullopt;
    }
    if(code.get_statement() == ID_decl)
    {
      // Variable declaration — initialize if has value
      if(code.operands().size() > 0 && code.op0().id() == ID_symbol)
      {
        const auto &sym = to_symbol_expr(code.op0());
        vars[sym.get_identifier()] = from_integer(0, sym.type());
      }
      return std::nullopt;
    }
    if(code.get_statement() == ID_expression)
      return std::nullopt; // side-effect expression, skip
    if(code.get_statement() == ID_skip)
      return std::nullopt;

    return std::nullopt; // unknown statement
  };

  auto result = execute(to_code(body), 0);
  if(result.has_value())
  {
    if(result->is_constant())
      return *result;
    // Reference-returning functions (like std::max) return
    // address_of(constant).  Unwrap to the constant.
    if(
      result->id() == ID_address_of &&
      to_address_of_expr(*result).object().is_constant())
    {
      return to_address_of_expr(*result).object();
    }
  }

  return nil_exprt();
}

struct_union_typet::componentt *cpp_typecheckt::ensure_member_complete(
  struct_union_typet &struct_type,
  const irep_idt &base_name)
{
  // Phase 1 of the lazy class-body elaboration refactor per N5008
  // [temp.inst]/3.  The full primitive will resolve a lazy
  // component's stored `cpp_declaration` / `cpp_declarator` source
  // (under `ID_lazy_type_source`) and replace its placeholder type
  // with the resolved one.  In Phase 1 no caller produces lazy
  // components, so the helper just locates the existing component
  // by base_name and returns it unchanged.
  //
  // The Phase 2 (caller audit) commits will route the ~12 readers
  // of `components()` that need a complete type through this helper
  // before reading `component.type()`.  Phase 3 enables the lazy
  // producer for class-template instances.
  for(auto &c : struct_type.components())
  {
    if(c.get_base_name() != base_name)
      continue;
    if(c.get_bool(ID_C_lazy_member_type))
    {
      // Reserved for Phase 3+: resolve the stored source.  No
      // producer marks components lazy in Phase 1, so this branch
      // is unreachable today.  When the producer lands, the body
      // will invoke `resolve_lazy_source` under a `sfinae_contextt`
      // guard ([temp.deduct]/8) and either complete the component
      // or return nullptr on substitution failure.
      UNREACHABLE;
    }
    return &c;
  }
  return nullptr;
}

void cpp_typecheckt::elaborate_class_template(
  const typet &type)
{
  if(type.id() != ID_struct_tag && type.id() != ID_union_tag)
    return;

  if(suppress_elaborate && !force_elaborate)
  {
    if(type.id() == ID_struct_tag || type.id() == ID_union_tag)
    {
      const symbolt &sym = lookup(to_tag_type(type));
      if(
        (sym.type.id() == ID_struct || sym.type.id() == ID_union) &&
        sym.type.get_bool(ID_template_class_instance) &&
        (to_struct_union_type(sym.type).components().empty() ||
         to_struct_union_type(sym.type).is_incomplete()))
      {
        // Empty or incomplete template instance — allow elaboration
      }
      else
        return;
    }
    else
      return;
  }

  const symbolt &symbol = lookup(to_tag_type(type));

  // Make a copy, as instantiate will destroy the symbol type!
  const typet t_type=symbol.type;

  // When force-elaborating empty template instances, catch errors
  // to avoid breaking callers. Errors in system header templates
  // (e.g., compressed_pair reference initialization) are non-fatal.

  if(
    (t_type.id() == ID_struct || t_type.id() == ID_union) &&
    t_type.get_bool(ID_template_class_instance))
  {
    // If the instance already has components and is fully elaborated
    // (not incomplete), skip re-instantiation.  Re-elaborating can
    // fail when template arguments reference local scopes that are
    // no longer accessible.  Partially elaborated classes (incomplete
    // with some components) must still be re-elaborated.
    if(
      !to_struct_union_type(symbol.type).components().empty() &&
      !to_struct_union_type(symbol.type).is_incomplete())
    {
      return;
    }

    const symbolt &initial_template = lookup(t_type.get(ID_identifier));
    // If the instance was created with a concept-constrained partial
    // specialization but is still empty, follow ID_specialization_of
    // to get the actual primary template. This re-does the
    // specialization search with concept evaluation, which may select
    // a more constrained specialization. Only do this for partial
    // specializations with concept constraints — full specializations
    // are always correct.
    bool has_concept_constraint = false;
    if(
      !initial_template.type.get(ID_specialization_of).empty() &&
      to_struct_union_type(symbol.type).components().empty())
    {
      const auto &tmpl_type =
        to_cpp_declaration(initial_template.type).template_type();
      for(const auto &p : tmpl_type.template_parameters())
        if(!p.get("#C_concept_constraint").empty())
          has_concept_constraint = true;
    }
    const symbolt &primary_template =
      has_concept_constraint
        ? lookup(initial_template.type.get(ID_specialization_of))
        : initial_template;

    // If this class template is already being instantiated with the
    // same arguments (on the instantiation stack), skip elaboration
    // to break infinite recursion. Also limit recursion depth for
    // the same primary template to prevent non-terminating chains.
    cpp_template_args_tct full_args =
      static_cast<const cpp_template_args_tct &>(
        t_type.find(ID_full_template_args));
    // Simplify non-type template arguments so that expressions like
    // is_destructible<T>::value are constant-folded before
    // specialization matching.
    for(auto &arg : full_args.arguments())
    {
      if(arg.id() != ID_type && arg.id() != ID_ambiguous)
      {
        try
        {
          typecheck_expr(arg);
          simplify(arg, *this);
          // Try constexpr evaluation for remaining function calls
          {
            std::function<void(exprt &)> eval_calls;
            eval_calls = [&](exprt &e)
            {
              for(auto &op : e.operands())
                eval_calls(op);
              if(
                e.id() == ID_side_effect &&
                e.get(ID_statement) == ID_function_call)
              {
                exprt r = try_evaluate_constexpr(e, symbol_table, *this);
                if(r.is_not_nil())
                  e = r;
              }
              simplify(e, *this);
            };
            eval_calls(arg);
          }
          // Resolve symbol references to their constant values
          if(arg.id() == ID_symbol)
          {
            const auto *sym =
              symbol_table.lookup(to_symbol_expr(arg).get_identifier());
            if(
              sym && sym->is_macro && sym->value.is_not_nil() &&
              sym->value.is_constant())
              arg = sym->value;
          }
        }
        catch(...)
        {
        }
      }
    }
    unsigned same_template_depth = 0;
    bool has_converging_int_args = false;
    for(const auto &entry : instantiation_stack)
    {
      if(entry.identifier == primary_template.name)
      {
        if(entry.full_template_args == full_args)
        {
          // Allow re-elaboration if the instance is empty
          // (primary template was used, specialization matching
          // hasn't happened yet).
          if(to_struct_union_type(symbol.type).components().empty())
            break; // proceed with specialization matching
          return;
        }
        ++same_template_depth;
      }
    }

    // For templates with non-type integer arguments that are strictly
    // smaller than all parent instances of the same template, allow
    // deeper recursion (convergent recursion like Fibonacci).
    // For type-only arguments, keep the conservative limit.
    if(same_template_depth >= 2)
    {
      // Check if current args have a non-type integer constant that
      // is strictly less than the corresponding arg in every parent.
      for(const auto &arg : full_args.arguments())
      {
        if(arg.id() == ID_type || !arg.is_constant())
          continue;
        mp_integer current_val;
        if(to_integer(to_constant_expr(arg), current_val))
          continue;
        bool all_parents_larger = true;
        for(const auto &entry : instantiation_stack)
        {
          if(entry.identifier != primary_template.name)
            continue;
          bool found_larger = false;
          for(const auto &parg : entry.full_template_args.arguments())
          {
            if(parg.id() == ID_type || !parg.is_constant())
              continue;
            mp_integer parent_val;
            if(to_integer(to_constant_expr(parg), parent_val))
              continue;
            if(parent_val > current_val)
            {
              found_larger = true;
              break;
            }
          }
          if(!found_larger)
          {
            all_parents_larger = false;
            break;
          }
        }
        if(all_parents_larger)
        {
          has_converging_int_args = true;
          break;
        }
      }
      if(!has_converging_int_args)
        return;
    }

    const cpp_template_args_tct &specialization_args =
      static_cast<const cpp_template_args_tct &>(
        t_type.find(ID_specialization_template_args));

    // Resolve symbol references in full_args, mirroring the logic
    // in template_suffix.
    cpp_template_args_tct full_args_tc = full_args;
    for(auto &arg : full_args_tc.arguments())
    {
      if(arg.id() == ID_type)
        continue;
      for(int pass = 0; pass < 10; ++pass)
      {
        bool changed = false;
        arg.visit_pre(
          [this, &changed](exprt &node)
          {
            if(node.id() == ID_symbol)
            {
              const symbolt &sym =
                lookup(to_symbol_expr(node).get_identifier());
              if(sym.value.is_not_nil() && cpp_is_pod(sym.type))
              {
                node = sym.value;
                changed = true;
              }
            }
          });
        if(!changed)
          break;
        simplify(arg, *this);
        if(arg.is_constant())
          break;
      }
    }

    // Search for a better-matching partial specialization only if
    // the symbol was created with the primary template (not already
    // matched to a partial specialization).
    const symbolt *best_match = &primary_template;
    cpp_template_args_tct best_spec_args = specialization_args;

    if(primary_template.type.get(ID_specialization_of).empty())
    {
      cpp_scopet *template_scope =
        id_map_lookup(cpp_scopes, primary_template.name);

      if(template_scope != nullptr)
      {
        cpp_scopet &scope = template_scope->get_parent();
        cpp_scopet::id_sett id_set =
          scope.lookup(primary_template.base_name, cpp_scopet::SCOPE_ONLY);

        // [temp.deduct]/8 + [temp.class.spec.match]: specialization
        // matching iterates candidate partial specializations; per-
        // candidate substitution failure is SFINAE, not a compile
        // error.
        sfinae_contextt spec_sfinae_guard{*this};

        for(const auto *id_ptr : id_set)
        {
          const symbolt &s = lookup(id_ptr->identifier);
          if(s.type.get(ID_specialization_of).empty())
            continue;

          const cpp_declarationt &cpp_declaration = to_cpp_declaration(s.type);
          const cpp_template_args_non_tct &partial_specialization_args =
            cpp_declaration.partial_specialization_args();

          if(
            partial_specialization_args.arguments().size() !=
            full_args_tc.arguments().size())
          {
            // Allow partial specialization to have more args than full
            // args when the extra args are variadic pack expansions
            // (which can match zero elements).
            bool size_ok = false;
            if(
              partial_specialization_args.arguments().size() >
              full_args_tc.arguments().size())
            {
              size_ok = true;
              for(std::size_t i = full_args_tc.arguments().size();
                  i < partial_specialization_args.arguments().size();
                  i++)
              {
                const auto &arg = partial_specialization_args.arguments()[i];
                if(
                  !arg.get_bool(ID_ellipsis) &&
                  !arg.type().get_bool(ID_ellipsis))
                {
                  size_ok = false;
                  break;
                }
              }
            }
            if(!size_ok)
              continue;
          }

          cpp_saved_template_mapt saved_map(template_map);
          cpp_save_scopet save_scope(cpp_scopes);

          template_map.build_unassigned(cpp_declaration.template_type());

          cpp_scopet *spec_scope = id_map_lookup(cpp_scopes, s.name);
          if(spec_scope != nullptr)
            cpp_scopes.go_to(*spec_scope);

          cpp_typecheck_resolvet resolver(*this);

          for(std::size_t i = 0; i < full_args_tc.arguments().size(); i++)
          {
            if(full_args_tc.arguments()[i].id() == ID_type)
              resolver.guess_template_args(
                partial_specialization_args.arguments()[i].type(),
                full_args_tc.arguments()[i].type());
            else
              resolver.guess_template_args(
                partial_specialization_args.arguments()[i],
                full_args_tc.arguments()[i]);
          }

          cpp_template_args_tct guessed_args =
            template_map.build_template_args(cpp_declaration.template_type());

          // Variadic pack parameters that matched zero elements
          // remain unassigned. Set them to empty type arguments.
          if(guessed_args.has_unassigned())
          {
            const auto &tparams =
              cpp_declaration.template_type().template_parameters();
            for(std::size_t i = 0; i < tparams.size(); i++)
            {
              if(
                i < guessed_args.arguments().size() &&
                tparams[i].get_bool(ID_ellipsis) &&
                (guessed_args.arguments()[i].id() == ID_unassigned ||
                 guessed_args.arguments()[i].type().id() == ID_unassigned))
              {
                guessed_args.arguments()[i] = exprt(ID_type, empty_typet());
              }
            }
          }

          if(guessed_args.has_unassigned())
            continue;

          // Evaluate requires clause (if present) with substituted args.
          // If the clause evaluates to false, skip this specialization.
          {
            const cpp_declarationt &spec_decl = to_cpp_declaration(s.type);
            const exprt &req_clause = static_cast<const exprt &>(
              spec_decl.template_type().find(ID_C_requires_clause));
            if(req_clause.is_not_nil() && req_clause.id() != ID_nil)
            {
              exprt req_copy = req_clause;
              template_map.apply(req_copy);
              // [temp.constr.atomic]/3: an unsatisfied atomic
              // constraint is a soft failure, not an ill-formed
              // program — treat typecheck errors here as SFINAE.
              bool satisfied = true;
              try
              {
                sfinae_contextt sfinae_guard{*this};
                typecheck_expr(req_copy);
                simplify(req_copy, *this);
                if(req_copy.is_false())
                  satisfied = false;
              }
              catch(...)
              {
                // Can't evaluate — treat as satisfied (backward compat)
              }
              if(!satisfied)
                continue;
            }

            // Check concept constraints on individual parameters.
            {
              const auto &spec_params =
                spec_decl.template_type().template_parameters();
              bool params_ok = true;
              for(std::size_t pi = 0; pi < spec_params.size() &&
                                      pi < full_args_tc.arguments().size();
                  ++pi)
              {
                const irep_idt &cc =
                  spec_params[pi].get("#C_concept_constraint");
                if(cc.empty())
                  continue;
                const auto concept_ids =
                  cpp_scopes.current_scope().lookup(cc, cpp_scopet::RECURSIVE);
                if(concept_ids.empty())
                  continue;
                const auto *concept_sym =
                  symbol_table.lookup((*concept_ids.begin())->identifier);
                if(!concept_sym || !concept_sym->type.get_bool(ID_is_template))
                  continue;
                const cpp_declarationt &concept_decl =
                  to_cpp_declaration(concept_sym->type);
                if(concept_decl.declarators().empty())
                  continue;
                exprt body = concept_decl.declarators()[0].value();
                if(body.is_nil())
                  continue;
                // Evaluate type_requirement nodes in the concept body.
                // Substitute the concept parameter with the actual type
                // and try to resolve each type requirement.
                template_mapt cmap;
                cpp_template_args_tct cargs;
                cargs.arguments().push_back(full_args_tc.arguments()[pi]);
                cmap.build(concept_decl.template_type(), cargs);
                // Create temporary symbols for requires-expression
                // parameters (e.g., requires(T t) { ++t; } needs 't').
                {
                  const irept &req_params = body.find("#requires_params");

                  for(const auto &param : req_params.get_sub())
                  {
                    irep_idt pname = param.get(ID_name);
                    if(pname.empty())
                      continue;
                    typet ptype =
                      static_cast<const typet &>(param.find(ID_type));
                    cmap.apply(ptype);
                    // [temp.constr.atomic]/3: substitution failure
                    // inside a requires-clause parameter type is a
                    // SFINAE failure (unsatisfied constraint), not
                    // a compilation error.
                    try
                    {
                      sfinae_contextt sfinae_guard{*this};
                      typecheck_type(ptype);
                    }
                    catch(...)
                    {
                    }
                    irep_idt id = "requires_param::" + id2string(pname);
                    if(!symbol_table.has_symbol(id))
                    {
                      symbolt param_sym{id, ptype, ID_cpp};
                      param_sym.base_name = pname;
                      param_sym.is_lvalue = true;
                      symbol_table.add(param_sym);
                    }
                    else
                    {
                      symbol_table.get_writeable_ref(id).type = ptype;
                    }
                    cpp_idt &scope_id =
                      cpp_scopes.current_scope().insert(pname);
                    scope_id.identifier = id;
                    scope_id.id_class = cpp_idt::id_classt::SYMBOL;
                  }
                }
                // Evaluate type_requirements by resolving types
                body.visit_pre(
                  [&](exprt &e)
                  {
                    // Handle nested concept references
                    // (cpp_name with template_args)
                    if(e.id() == ID_cpp_name && params_ok)
                    {
                      bool has_targs = false;
                      for(const auto &s : e.get_sub())
                        if(s.id() == ID_template_args)
                          has_targs = true;
                      if(has_targs)
                      {
                        exprt copy = e;
                        cmap.apply(copy);
                        // [temp.constr.atomic]/3: per-candidate
                        // concept check is SFINAE-guarded.
                        try
                        {
                          sfinae_contextt sfinae_guard{*this};
                          typecheck_expr(copy);
                          simplify(copy, *this);
                          if(copy.is_true())
                            e = typecast_exprt{true_exprt(), c_bool_type()};
                          else
                            params_ok = false;
                        }
                        catch(...)
                        {
                          params_ok = false;
                        }
                      }
                    }
                    if(e.id() == "type_requirement" && params_ok)
                    {
                      typet t = static_cast<const typet &>(e.find(ID_type_arg));
                      cmap.apply(t);
                      // [expr.prim.req.type]/1 + [temp.deduct]/8:
                      // a type requirement is satisfied iff the
                      // type-id is valid; substitution failure is
                      // a SFINAE failure.
                      try
                      {
                        sfinae_contextt sfinae_guard{*this};
                        typecheck_type(t);
                        e = typecast_exprt{true_exprt(), c_bool_type()};
                      }
                      catch(...)
                      {
                        params_ok = false;
                      }
                    }
                    // Simple requirement: check if expression type-checks
                    if(e.id() == "simple_requirement" && params_ok)
                    {
                      exprt expr_copy = to_unary_expr(e).op();
                      cmap.apply(expr_copy);
                      // [expr.prim.req.simple]/1 + [temp.deduct]/8:
                      // a simple requirement is satisfied iff the
                      // expression is valid; substitution failure
                      // is SFINAE.
                      try
                      {
                        sfinae_contextt sfinae_guard{*this};
                        typecheck_expr(expr_copy);
                        e = typecast_exprt{true_exprt(), c_bool_type()};
                      }
                      catch(...)
                      {
                        params_ok = false;
                      }
                    }
                    // Compound requirement: check expression type-checks
                    // and result type satisfies constraint
                    if(e.id() == "compound_requirement" && params_ok)
                    {
                      exprt expr_copy = to_unary_expr(e).op();
                      cmap.apply(expr_copy);
                      // [expr.prim.req.compound] + [temp.deduct]/8:
                      // a compound requirement checks that the
                      // expression is valid AND (if a trailing
                      // return-type constraint is present) that the
                      // result satisfies it.  Both checks are
                      // SFINAE-guarded.
                      bool ok = true;
                      try
                      {
                        sfinae_contextt sfinae_guard{*this};
                        typecheck_expr(expr_copy);
                        // Check return type constraint if present
                        const irept &constraint = e.find("#constraint");
                        if(constraint.is_not_nil())
                        {
                          // Per [expr.prim.req.compound], prepend
                          // decltype((expr)) to constraint template args.
                          typet result_type = expr_copy.type();
                          if(expr_copy.get_bool(ID_C_lvalue))
                            result_type = reference_type(result_type);
                          // Look up the concept and evaluate directly
                          irep_idt concept_name;
                          for(const auto &sub : constraint.get_sub())
                            if(sub.id() == ID_name)
                              concept_name = sub.get(ID_identifier);
                          if(!concept_name.empty())
                          {
                            auto cids = cpp_scopes.current_scope().lookup(
                              concept_name, cpp_scopet::RECURSIVE);
                            for(const auto *cid : cids)
                            {
                              const auto *csym =
                                symbol_table.lookup(cid->identifier);
                              if(!csym || !csym->type.get_bool(ID_is_template))
                                continue;
                              const auto &cd = to_cpp_declaration(csym->type);
                              if(cd.declarators().empty())
                                continue;
                              exprt cbody = cd.declarators()[0].value();
                              if(cbody.is_nil())
                                continue;
                              // Build template args: prepend result_type
                              // to the constraint's existing args
                              cpp_template_args_tct check_args;
                              exprt ta{ID_type};
                              ta.type() = result_type;
                              check_args.arguments().push_back(std::move(ta));
                              for(const auto &sub : constraint.get_sub())
                              {
                                if(sub.id() == ID_template_args)
                                {
                                  const auto &args_sub = sub.find(ID_arguments);
                                  for(const auto &a : args_sub.get_sub())
                                  {
                                    exprt arg_copy =
                                      static_cast<const exprt &>(a);
                                    cmap.apply(arg_copy);
                                    typecheck_type(arg_copy.type());
                                    check_args.arguments().push_back(
                                      std::move(arg_copy));
                                  }
                                }
                              }
                              template_mapt cmap2;
                              cmap2.build(cd.template_type(), check_args);
                              cmap2.apply(cbody);

                              typecheck_expr(cbody);
                              simplify(cbody, *this);
                              if(cbody.is_false())
                                ok = false;
                              break;
                            }
                          }
                        }
                      }
                      catch(...)
                      {
                        ok = false;
                      }
                      if(ok)
                        e = typecast_exprt{true_exprt(), c_bool_type()};
                      else
                        params_ok = false;
                    }
                  });
                if(!params_ok)
                  break;
                // Evaluate the concept body after type_requirement
                // and cpp_name nodes have been resolved.  Per
                // [temp.constr.constr]: the concept is satisfied
                // iff the body evaluates to `true` — substitution
                // failures are SFINAE failures.
                cmap.apply(body);
                bool old_suppress2 = suppress_elaborate;
                suppress_elaborate = false;
                try
                {
                  sfinae_contextt sfinae_guard{*this};
                  typecheck_expr(body);
                  simplify(body, *this);
                  if(body.is_false())
                    params_ok = false;
                }
                catch(...)
                {
                  params_ok = false;
                }
                suppress_elaborate = old_suppress2;
              }
              if(!params_ok)
                continue;
            }
          }

          // Typecheck the partial specialization args with the guessed
          // values, using the primary template for type context.
          // If typechecking fails (e.g., accessing a member of a
          // non-class type), treat it as a substitution failure
          // (SFINAE) and skip this specialization.
          cpp_template_args_tct partial_specialization_args_tc;
          bool sfinae_failed = false;
          {
            // Per [temp.inst]/1 + [temp.deduct]/8: partial
            // specialization matching uses template-argument
            // deduction, so substitution failure is SFINAE.
            // Suppress eager elaboration to avoid instantiating
            // unused branches (e.g. conditional_t's false branch).
            bool old_suppress = suppress_elaborate;
            suppress_elaborate = true;
            try
            {
              sfinae_contextt sfinae_guard{*this};
              partial_specialization_args_tc = typecheck_template_args(
                type.source_location(),
                primary_template,
                partial_specialization_args);
            }
            catch(...)
            {
              sfinae_failed = true;
            }
            suppress_elaborate = old_suppress;
          }
          if(sfinae_failed)
            continue;

          // Strip ellipsis flags from cpp_declaration declarators in
          // code type arguments (variadic pack residue).
          for(auto &arg : partial_specialization_args_tc.arguments())
          {
            if(arg.id() != ID_type || arg.type().id() != ID_code)
              continue;
            for(auto &param : arg.type().add(ID_parameters).get_sub())
            {
              if(param.id() != ID_cpp_declaration)
                continue;
              for(auto &decl :
                  static_cast<cpp_declarationt &>(param).declarators())
                decl.remove(ID_ellipsis);
            }
          }

          // Remove trailing pack expansion args from the type-checked
          // partial specialization args that correspond to empty packs
          // in the original (non-type-checked) partial specialization.
          {
            const auto &orig_args = partial_specialization_args.arguments();
            auto &tc_args = partial_specialization_args_tc.arguments();
            while(tc_args.size() > full_args_tc.arguments().size() &&
                  !tc_args.empty() && tc_args.size() <= orig_args.size())
            {
              std::size_t idx = tc_args.size() - 1;
              const auto &orig = orig_args[idx];
              if(
                orig.get_bool(ID_ellipsis) || orig.type().get_bool(ID_ellipsis))
              {
                tc_args.pop_back();
              }
              else
                break;
            }
          }

          if(
            partial_specialization_args_tc.arguments() ==
            full_args_tc.arguments())
          {
            // operator== on irept ignores #-prefixed attributes like
            // C_constant and C_volatile. Check them recursively on
            // the type tree so that e.g. const T* and T* partial
            // specializations are correctly distinguished.
            bool qualifiers_match = true;
            for(std::size_t j = 0;
                j < partial_specialization_args_tc.arguments().size();
                j++)
            {
              const exprt &p = partial_specialization_args_tc.arguments()[j];
              const exprt &f = full_args_tc.arguments()[j];
              if(p.id() == ID_type)
              {
                if(!qualifiers_match_recursively(p.type(), f.type()))
                {
                  qualifiers_match = false;
                  break;
                }
              }
            }
            if(!qualifiers_match)
              continue;
            // Check if this specialization is more specialized than
            // the current best match. A specialization is more
            // specialized if its pattern has more constrained
            // arguments (e.g., pack<Rp...> vs plain Rp).
            if(best_match == &primary_template)
            {
              best_match = &s;
              best_spec_args = guessed_args;
            }
            else
            {
              const cpp_declarationt &best_decl =
                to_cpp_declaration(best_match->type);
              const cpp_template_args_non_tct &best_partial_args =
                best_decl.partial_specialization_args();

              // Count non-trivial arguments. A cpp_name with template
              // args (e.g., pack<Rp...>) counts as constrained.
              auto count_constrained = [](const cpp_template_args_non_tct &args)
              {
                std::size_t count = 0;
                for(const auto &arg : args.arguments())
                {
                  const irept *a = &arg;
                  if(a->id() == ID_type)
                    a = &arg.type();
                  if(a->id() == ID_ambiguous)
                    a = &a->find(ID_type);

                  if(a->id() != ID_cpp_name)
                  {
                    count++;
                  }
                  else
                  {
                    for(const auto &sub : a->get_sub())
                      if(sub.id() == ID_template_args)
                      {
                        count++;
                        break;
                      }
                  }
                }
                return count;
              };

              if(
                count_constrained(partial_specialization_args) >
                count_constrained(best_partial_args))
              {
                best_match = &s;
                best_spec_args = guessed_args;
              }
              // Prefer specialization with fewer args (more specific)
              // when constraint counts are equal.
              else if(
                count_constrained(partial_specialization_args) ==
                  count_constrained(best_partial_args) &&
                partial_specialization_args.arguments().size() <
                  best_partial_args.arguments().size())
              {
                best_match = &s;
                best_spec_args = guessed_args;
              }
              // C++ [temp.class.order]: when argument patterns are equal,
              // prefer the more constrained specialization. A specialization
              // with a simpler concept constraint (fewer requires clauses)
              // is more constrained than one with additional negations.
              else if(
                count_constrained(partial_specialization_args) ==
                  count_constrained(best_partial_args) &&
                partial_specialization_args.arguments().size() ==
                  best_partial_args.arguments().size())
              {
                const auto &s_req =
                  cpp_declaration.template_type().get(ID_C_requires_clause);
                const auto &best_req =
                  best_decl.template_type().get(ID_C_requires_clause);
                // Prefer the specialization with fewer constraints
                // (simpler concept = more specific).
                // A requires clause count of "1" is simpler than "2".
                int s_count = 0, best_count = 0;
                if(!s_req.empty() && isdigit(id2string(s_req)[0]))
                  s_count = std::stoi(id2string(s_req));
                if(!best_req.empty() && isdigit(id2string(best_req)[0]))
                  best_count = std::stoi(id2string(best_req));
                // Also count concept constraints on parameters
                for(const auto &p :
                    cpp_declaration.template_type().template_parameters())
                  if(!p.get("#C_concept_constraint").empty())
                    s_count++;
                for(const auto &p :
                    best_decl.template_type().template_parameters())
                  if(!p.get("#C_concept_constraint").empty())
                    best_count++;
                if(s_count < best_count)
                {
                  best_match = &s;
                  best_spec_args = guessed_args;
                }
              }
            }
          }
        }
      }
    }

    // Catch instantiation errors to preserve partially-completed types.
    // Template instantiation creates the struct body (components) first,
    // then processes method bodies which may fail for system headers.
    // Without catching, the exception propagates and the caller sees
    // the type as incomplete even though the struct body is complete.
    // C++20: evaluate requires clause on the selected specialization.
    if(!best_match->type.get(ID_specialization_of).empty())
    {
      const cpp_declarationt &spec_decl = to_cpp_declaration(best_match->type);
      const exprt &req_clause = static_cast<const exprt &>(
        spec_decl.template_type().find(ID_C_requires_clause));
      if(req_clause.is_not_nil() && req_clause.id() != ID_nil)
      {
        // Build parameter name -> actual type mapping
        const auto &params = spec_decl.template_type().template_parameters();
        std::map<irep_idt, typet> param_map;
        for(std::size_t i = 0;
            i < params.size() && i < full_args_tc.arguments().size();
            ++i)
        {
          if(params[i].id() == ID_type)
          {
            const std::string id_str =
              id2string(params[i].type().get(ID_identifier));
            auto pos = id_str.rfind("::");
            irep_idt pname = pos != std::string::npos
                               ? irep_idt{id_str.substr(pos + 2)}
                               : irep_idt{id_str};
            if(!pname.empty())
              param_map[pname] = full_args_tc.arguments()[i].type();
          }
        }

        // Resolve a type from a cpp_name or type_exprt
        std::function<typet(const irept &)> resolve_type =
          [&](const irept &node) -> typet
        {
          if(node.id() == ID_type)
            return static_cast<const type_exprt &>(
                     static_cast<const exprt &>(node))
              .type();
          if(node.id() == ID_cpp_name)
          {
            for(const auto &s : node.get_sub())
              if(s.id() == ID_name)
              {
                auto it = param_map.find(s.get(ID_identifier));
                if(it != param_map.end())
                  return it->second;
              }
          }
          return typet{};
        };

        // Evaluate a requires clause expression with substituted types
        std::function<int(const irept &)> eval = [&](const irept &node) -> int
        {
          // -1 = can't evaluate, 0 = false, 1 = true
          if(node.id() == ID_and)
          {
            for(const auto &sub : node.get_sub())
            {
              int v = eval(sub);
              if(v == 0)
                return 0;
              if(v == -1)
                return -1;
            }
            return 1;
          }
          if(node.id() == ID_or)
          {
            for(const auto &sub : node.get_sub())
            {
              int v = eval(sub);
              if(v == 1)
                return 1;
              if(v == -1)
                return -1;
            }
            return 0;
          }
          if(node.id() == ID_not)
          {
            if(node.get_sub().empty())
              return -1;
            int v = eval(node.get_sub()[0]);
            return v == -1 ? -1 : (v == 0 ? 1 : 0);
          }
          // side_effect(statement=function_call) with cpp_name as function
          if(node.id() == ID_side_effect)
          {
            const auto &subs = node.get_sub();
            if(subs.size() >= 2 && subs[0].id() == ID_cpp_name)
            {
              irep_idt fname;
              for(const auto &s : subs[0].get_sub())
                if(s.id() == ID_name)
                  fname = s.get(ID_identifier);
              // Get the argument type
              const auto &args = subs[1].get_sub();
              if(args.empty())
                return -1;
              // For __remove_pointer, evaluate the inner call first
              typet arg_type;
              if(args[0].id() == ID_side_effect)
              {
                // Nested call like __remove_pointer(T)
                irep_idt inner_fname;
                const auto &inner_subs = args[0].get_sub();
                if(inner_subs.size() >= 2 && inner_subs[0].id() == ID_cpp_name)
                {
                  for(const auto &s : inner_subs[0].get_sub())
                    if(s.id() == ID_name)
                      inner_fname = s.get(ID_identifier);
                  const auto &inner_args = inner_subs[1].get_sub();
                  if(!inner_args.empty())
                  {
                    typet inner_type = resolve_type(inner_args[0]);
                    if(inner_type.is_nil())
                      return -1;
                    if(inner_fname == "__remove_pointer")
                    {
                      if(inner_type.id() == ID_pointer)
                        arg_type = to_pointer_type(inner_type).base_type();
                      else
                        return -1;
                    }
                    else
                      return -1;
                  }
                  else
                    return -1;
                }
                else
                  return -1;
              }
              else
              {
                arg_type = resolve_type(args[0]);
              }
              if(arg_type.is_nil())
                return -1;
              if(fname == "__is_pointer")
                return arg_type.id() == ID_pointer ? 1 : 0;
              if(fname == "__is_integral")
                return (arg_type.id() == ID_signedbv ||
                        arg_type.id() == ID_unsignedbv ||
                        arg_type.id() == ID_bool || arg_type.id() == ID_c_bool)
                         ? 1
                         : 0;
              if(fname == "__is_signed")
                return arg_type.id() == ID_signedbv ? 1 : 0;
            }
          }
          return -1;
        };

        int result = eval(req_clause);
        if(result == 0)
        {
          // Requires clause is false — try other specializations
          const irep_idt &prim_name =
            best_match->type.get(ID_specialization_of);
          const auto *primary = symbol_table.lookup(prim_name);
          if(primary)
          {
            const symbolt *fallback = primary;
            // Search for a satisfied specialization
            cpp_scopet *ts = id_map_lookup(cpp_scopes, prim_name);
            if(ts)
            {
              cpp_scopet &scope = ts->get_parent();
              cpp_scopet::id_sett id_set =
                scope.lookup(primary->base_name, cpp_scopet::SCOPE_ONLY);
              for(const auto *id_ptr : id_set)
              {
                const symbolt &s = lookup(id_ptr->identifier);
                if(s.type.get(ID_specialization_of).empty())
                  continue;
                if(&s == best_match)
                  continue;
                const cpp_declarationt &sd = to_cpp_declaration(s.type);
                const exprt &rc = static_cast<const exprt &>(
                  sd.template_type().find(ID_C_requires_clause));
                if(rc.is_nil() || rc.id() == ID_nil)
                  continue;
                int rv = eval(rc);
                if(rv == 1)
                {
                  fallback = &s;
                  break;
                }
              }
            }
            best_match = fallback;
            best_spec_args = full_args;
          }
        }
      }
    }

    // Re-check: the symbol may have been elaborated by a recursive
    // call during the specialization matching above.  Per the
    // standard, a class template specialization that is already
    // complete should not be re-instantiated.
    {
      const symbolt &sym_now = lookup(to_tag_type(type));
      if(
        (sym_now.type.id() == ID_struct || sym_now.type.id() == ID_union) &&
        !to_struct_union_type(sym_now.type).components().empty() &&
        !to_struct_union_type(sym_now.type).is_incomplete())
      {
        return;
      }
    }

    instantiate_template(
      type.source_location(), *best_match, best_spec_args, full_args);
  }
}

/// Instantiate a template with the given arguments.
///
/// Implements [temp.inst]: implicit instantiation of class and function
/// templates.  For class templates, creates the class symbol with
/// substituted template arguments and processes the class body
/// ([temp.mem.func], [temp.mem.class], [temp.static]).  For function
/// templates, creates the function symbol with substituted types.
///
/// Template argument substitution follows [temp.deduct.type]: the
/// template_map is used to replace template parameters with their
/// deduced or explicitly specified values.
///
/// \param source_location: location of the instantiation
/// \param template_symbol: the template being instantiated
/// \param specialization_template_args: typechecked template arguments
/// \param full_template_args: full set of template arguments
/// \param specialization: optional explicit specialization type
#define MAX_DEPTH 50

const symbolt &cpp_typecheckt::instantiate_template(
  const source_locationt &source_location,
  const symbolt &template_symbol,
  const cpp_template_args_tct &specialization_template_args,
  const cpp_template_args_tct &full_template_args,
  const typet &specialization)
{
#ifdef DEBUG
  std::cout << "instantiate_template: " << template_symbol.name << '\n';
#endif

  if(instantiation_stack.size()==MAX_DEPTH)
  {
    show_instantiation_stack(error());
    error().source_location=source_location;
    error() << "reached maximum template recursion depth ("
            << MAX_DEPTH << ")" << eom;
    throw 0;
  }

  instantiation_levelt i_level(instantiation_stack, had_template_instantiation);
  instantiation_stack.back().source_location=source_location;
  instantiation_stack.back().identifier=template_symbol.name;
  instantiation_stack.back().full_template_args=full_template_args;

#ifdef DEBUG
  std::cout << "L: " << source_location << '\n';
  std::cout << "I: " << template_symbol.name << '\n';
#endif

  cpp_saved_template_mapt saved_map(template_map);

  bool specialization_given=specialization.is_not_nil();

  // If specialization arguments still contain unassigned template
  // parameters, this is a substitution failure during template
  // instantiation (per [temp.deduct]).  Throw silently so that
  // SFINAE and overload resolution can try other candidates
  // instead of reporting a hard error.
  if(specialization_template_args.has_unassigned())
    throw 0;
  DATA_INVARIANT(
    !full_template_args.has_unassigned(), "should never get 'unassigned' here");

#ifdef DEBUG
  std::cout << "A: <";
  forall_expr(it, specialization_template_args.arguments())
  {
    if(it!=specialization_template_args.arguments().begin())
      std::cout << ", ";
    if(it->id()==ID_type)
      std::cout << to_string(it->type());
    else
      std::cout << to_string(*it);
  }
  std::cout << ">\n\n";
#endif

  // do we have arguments?
  if(full_template_args.arguments().empty())
  {
    // Empty args are valid for:
    // 1. Variadic templates with zero arguments (e.g., tuple<>)
    // 2. Explicit specializations with zero parameters
    const template_typet &template_type =
      to_cpp_declaration(template_symbol.type).template_type();
    const auto &params = template_type.template_parameters();
    bool valid_empty = params.empty();
    if(!valid_empty)
    {
      valid_empty = true;
      for(const auto &p : params)
      {
        if(!p.get_bool(ID_ellipsis))
        {
          valid_empty = false;
          break;
        }
      }
    }
    if(!valid_empty)
    {
      error().source_location = source_location;
      error() << "'" << template_symbol.base_name
              << "' is a template; thus, expected template arguments" << eom;
      throw 0;
    }
  }

  // produce new symbol name
  std::string suffix=template_suffix(full_template_args);

  // we need the template scope to see the template parameters
  cpp_scopet *template_scope = id_map_lookup(cpp_scopes, template_symbol.name);

  if(template_scope==nullptr)
  {
    error().source_location=source_location;
    error() << "template scope '" << template_symbol.base_name << "' not found"
            << eom;
    throw 0;
  }

  // [temp.point] p1: When a function template is instantiated, the
  // definition (not just a forward declaration) must be used.  If the
  // template_symbol is a forward declaration (no body), search the
  // parent scope for the definition of the same template.
  const symbolt *effective_template = &template_symbol;
  {
    const cpp_declarationt &check_decl =
      to_cpp_declaration(template_symbol.type);
    if(
      !check_decl.declarators().empty() &&
      check_decl.declarators()[0].value().is_nil())
    {
      cpp_scopet &parent = template_scope->get_parent();
      cpp_scopet::id_sett id_set =
        parent.lookup(template_symbol.base_name, cpp_scopet::SCOPE_ONLY);
      for(const auto *id_ptr : id_set)
      {
        if(id_ptr->identifier == template_symbol.name)
          continue;
        const symbolt *candidate = symbol_table.lookup(id_ptr->identifier);
        if(
          candidate != nullptr && candidate->type.get_bool(ID_is_template) &&
          candidate->base_name == template_symbol.base_name)
        {
          const cpp_declarationt &cand_decl =
            to_cpp_declaration(candidate->type);
          if(
            !cand_decl.declarators().empty() &&
            cand_decl.declarators()[0].value().is_not_nil())
          {
            effective_template = candidate;
            template_scope = id_map_lookup(cpp_scopes, candidate->name);
            break;
          }
        }
      }
    }
  }

  // produce new declaration
  cpp_declarationt new_decl = to_cpp_declaration(effective_template->type);

  // The new one is not a template any longer, but we remember the
  // template type that was used.
  template_typet template_type=new_decl.template_type();
  new_decl.remove(ID_is_template);
  new_decl.remove(ID_template_type);
  new_decl.set(ID_C_template, template_symbol.name);
  new_decl.set(ID_C_template_arguments, specialization_template_args);

  // save old scope
  cpp_save_scopet saved_scope(cpp_scopes);

  // mapping from template parameters to values/types
  template_map.build(template_type, specialization_template_args);

  // Per [temp.variadic]/7: for constructor templates with variadic packs,
  // remove empty pack parameters and substitute non-empty pack names.
  if(!template_map.pack_size_map.empty() && !new_decl.declarators().empty())
  {
    bool has_variadic = false;
    for(const auto &p : template_type.template_parameters())
      if(p.get_bool(ID_ellipsis))
        has_variadic = true;
    // Apply pack removal to all function templates with variadic packs
    // per [temp.variadic]/7.
    if(!has_variadic)
      goto skip_pack_removal;

    // Only collect empty pack names from THIS template's parameters
    std::set<std::string> ep_names;
    for(const auto &tp : template_type.template_parameters())
    {
      if(!tp.get_bool(ID_ellipsis))
        continue;
      irep_idt pid = tp.type().get(ID_identifier);
      if(pid.empty())
        continue;
      auto it = template_map.pack_size_map.find(pid);
      if(it != template_map.pack_size_map.end() && it->second == 0)
      {
        const std::string f = id2string(pid);
        auto p = f.rfind("::");
        ep_names.insert(p != std::string::npos ? f.substr(p + 2) : f);
      }
    }
    if(!ep_names.empty())
    {
      std::function<bool(const irept &)> refs_ep = [&](const irept &n) -> bool
      {
        if(n.id() == ID_template_parameter_symbol_type)
        {
          const std::string f = id2string(n.get(ID_identifier));
          auto p = f.rfind("::");
          if(ep_names.count(p != std::string::npos ? f.substr(p + 2) : f))
            return true;
        }
        if(n.id() == ID_name && ep_names.count(id2string(n.get(ID_identifier))))
          return true;
        for(const auto &s : n.get_sub())
          if(refs_ep(s))
            return true;
        for(const auto &ns : n.get_named_sub())
          if(refs_ep(ns.second))
            return true;
        return false;
      };
      auto &decl = new_decl.declarators()[0];
      if(decl.type().id() == ID_function_type)
      {
        irept &params = decl.type().add(ID_parameters);
        params.get_sub().erase(
          std::remove_if(
            params.get_sub().begin(),
            params.get_sub().end(),
            [&](const irept &p)
            {
              if(p.id() != ID_cpp_declaration)
                return false;
              for(const auto &d : p.get_sub())
                if(
                  d.id() == ID_cpp_declarator &&
                  (d.find(ID_type).get_bool(ID_ellipsis) ||
                   d.get_bool(ID_ellipsis) || refs_ep(d)))
                  return true;
              return refs_ep(p.find(ID_type));
            }),
          params.get_sub().end());
      }
      irept &mi = decl.add(ID_member_initializers);
      for(auto &init : mi.get_sub())
      {
        auto &subs = init.get_sub();
        subs.erase(
          std::remove_if(
            subs.begin(),
            subs.end(),
            [&](const irept &s) { return refs_ep(s); }),
          subs.end());
      }
    }
    // Per [temp.variadic]/7: for non-empty packs, substitute
    // pack parameter names with actual type base names and
    // remove ellipsis from expanded expressions.
    if(!template_map.pack_args_map.empty())
    {
      std::map<std::string, irep_idt> pack_subst;
      for(const auto &pa : template_map.pack_args_map)
      {
        if(pa.second.empty())
          continue;
        const std::string full = id2string(pa.first);
        auto p = full.rfind("::");
        const std::string sn =
          p != std::string::npos ? full.substr(p + 2) : full;
        const typet &t = pa.second.front();
        if(t.id() == ID_struct_tag)
        {
          std::string tag = id2string(to_struct_tag_type(t).get_identifier());
          if(tag.substr(0, 4) == "tag-")
            tag = tag.substr(4);
          auto tag_pos = tag.find("tag-");
          if(tag_pos != std::string::npos)
            tag = tag.substr(0, tag_pos) + tag.substr(tag_pos + 4);
          auto last_sep = tag.rfind("::");
          if(last_sep != std::string::npos)
            tag = tag.substr(last_sep + 2);
          pack_subst[sn] = tag;
        }
      }
      if(!pack_subst.empty() && !new_decl.declarators().empty())
      {
        std::function<bool(const irept &)> contains_pack =
          [&](const irept &node) -> bool
        {
          if(
            node.id() == ID_name &&
            pack_subst.count(id2string(node.get(ID_identifier))))
            return true;
          for(const auto &s : node.get_sub())
            if(contains_pack(s))
              return true;
          for(const auto &ns : node.get_named_sub())
            if(contains_pack(ns.second))
              return true;
          return false;
        };
        std::function<void(irept &)> subst = [&](irept &node)
        {
          if(
            node.id() == ID_name &&
            pack_subst.count(id2string(node.get(ID_identifier))))
          {
            node.set(
              ID_identifier, pack_subst.at(id2string(node.get(ID_identifier))));
          }
          for(auto &s : node.get_sub())
            subst(s);
          for(auto &ns : node.get_named_sub())
            subst(ns.second);
        };
        irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
        subst(mi);
        // Remove ellipsis only from pack-expanded parameters
        auto &dt = new_decl.declarators()[0].type();
        if(dt.id() == ID_function_type)
        {
          irept &params = dt.add(ID_parameters);
          for(auto &p : params.get_sub())
          {
            if(contains_pack(p))
            {
              subst(p);
              p.remove(ID_ellipsis);
              for(auto &d : p.get_sub())
                d.remove(ID_ellipsis);
            }
          }
        }
      }
    }
  }
skip_pack_removal:

  // Per [temp.variadic]/7: when a variadic pack is empty, remove
  // pack-expanded parameters from the function type and remove
  // member initializer expressions referencing the empty pack.
  // This must happen immediately after build() sets pack_size_map,
  // before any code that might try to resolve the pack parameter.
  if(!template_map.pack_size_map.empty() && !new_decl.declarators().empty())
  {
    // Only apply for constructor templates with variadic packs
    bool has_variadic = false;
    for(const auto &p : template_type.template_parameters())
      if(p.get_bool(ID_ellipsis))
        has_variadic = true;
    bool is_ctor = new_decl.is_constructor();
    if(!has_variadic || !is_ctor)
      goto skip_pack_removal_ft;

    // Only collect empty pack names from THIS template's parameters
    std::set<std::string> ep_names;
    for(const auto &tp : template_type.template_parameters())
    {
      if(!tp.get_bool(ID_ellipsis))
        continue;
      irep_idt pid = tp.type().get(ID_identifier);
      if(pid.empty())
        continue;
      auto it = template_map.pack_size_map.find(pid);
      if(it != template_map.pack_size_map.end() && it->second == 0)
      {
        const std::string f = id2string(pid);
        auto p = f.rfind("::");
        ep_names.insert(p != std::string::npos ? f.substr(p + 2) : f);
      }
    }
    if(!ep_names.empty())
    {
      std::function<bool(const irept &)> refs_ep = [&](const irept &n) -> bool
      {
        if(n.id() == ID_template_parameter_symbol_type)
        {
          const std::string f = id2string(n.get(ID_identifier));
          auto p = f.rfind("::");
          if(ep_names.count(p != std::string::npos ? f.substr(p + 2) : f))
            return true;
        }
        if(n.id() == ID_name && ep_names.count(id2string(n.get(ID_identifier))))
          return true;
        for(const auto &s : n.get_sub())
          if(refs_ep(s))
            return true;
        for(const auto &ns : n.get_named_sub())
          if(refs_ep(ns.second))
            return true;
        return false;
      };
      auto &decl = new_decl.declarators()[0];
      // Remove pack params from function type
      if(decl.type().id() == ID_function_type)
      {
        irept &params = decl.type().add(ID_parameters);
        params.get_sub().erase(
          std::remove_if(
            params.get_sub().begin(),
            params.get_sub().end(),
            [&](const irept &p)
            {
              if(p.id() != ID_cpp_declaration)
                return false;
              for(const auto &d : p.get_sub())
                if(
                  d.id() == ID_cpp_declarator &&
                  (d.find(ID_type).get_bool(ID_ellipsis) ||
                   d.get_bool(ID_ellipsis) || refs_ep(d)))
                  return true;
              return refs_ep(p.find(ID_type));
            }),
          params.get_sub().end());
      }
      // Remove empty pack expressions from member initializers
      irept &mi = decl.add(ID_member_initializers);
      for(auto &init : mi.get_sub())
      {
        auto &subs = init.get_sub();
        subs.erase(
          std::remove_if(
            subs.begin(),
            subs.end(),
            [&](const irept &s) { return refs_ep(s); }),
          subs.end());
      }
    }
    // Per [temp.variadic]/7: for non-empty packs, substitute
    // the pack parameter name in template_args with the actual
    // type from pack_args_map.
    if(!template_map.pack_args_map.empty())
    {
      // Build substitution map: short_name → type identifier
      std::map<std::string, irep_idt> pack_subst;
      for(const auto &pa : template_map.pack_args_map)
      {
        if(pa.second.empty())
          continue;
        const std::string full = id2string(pa.first);
        auto p = full.rfind("::");
        const std::string sn =
          p != std::string::npos ? full.substr(p + 2) : full;
        // For single-element packs, get the type's name
        const typet &t = pa.second.front();
        if(t.id() == ID_struct_tag)
        {
          std::string tag = id2string(to_struct_tag_type(t).get_identifier());
          if(tag.substr(0, 4) == "tag-")
            tag = tag.substr(4);
          pack_subst[sn] = tag;
        }
      }
      if(!pack_subst.empty() && !new_decl.declarators().empty())
      {
        // Substitute in member initializers
        std::function<void(irept &)> subst = [&](irept &node)
        {
          if(
            node.id() == ID_name &&
            pack_subst.count(id2string(node.get(ID_identifier))))
          {
            node.set(
              ID_identifier, pack_subst.at(id2string(node.get(ID_identifier))));
          }
          for(auto &s : node.get_sub())
            subst(s);
          for(auto &ns : node.get_named_sub())
            subst(ns.second);
        };
        irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
        subst(mi);
      }
    }
  }
skip_pack_removal_ft:

  // enter the template scope
  cpp_scopes.go_to(*template_scope);

  // For nested member class templates (e.g., Outer<int>::Inner<double>),
  // the outer template parameters (T) need to be in the template map
  // so that references to T in Inner's body can be resolved.
  if(new_decl.type().id() == ID_struct || new_decl.type().id() == ID_union)
  {
    cpp_scopet *scope = &template_scope->get_parent();
    while(scope != nullptr && !scope->is_root_scope())
    {
      if(scope->is_class())
      {
        const auto *class_sym = symbol_table.lookup(scope->identifier);
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
      }
      scope = &scope->get_parent();
    }
  }

  // Is it a template method?
  // It's in the scope of a class, and not a class itself.
  bool is_template_method =
    cpp_scopes.current_scope().get_parent().is_class() &&
    new_decl.type().id() != ID_struct && new_decl.type().id() != ID_union;

  irep_idt class_name;

  if(is_template_method)
    class_name=cpp_scopes.current_scope().get_parent().identifier;

  // sub-scope for fixing the prefix
  cpp_scopet &sub_scope = sub_scope_for_instantiation(*template_scope, suffix);

  // let's see if we have the instance already
  {
    cpp_scopet::id_sett id_set =
      sub_scope.lookup(template_symbol.base_name, cpp_scopet::SCOPE_ONLY);

    if(id_set.size()==1)
    {
      // It has already been instantiated!
      const cpp_idt &cpp_id = **id_set.begin();

      DATA_INVARIANT(
        cpp_id.id_class == cpp_idt::id_classt::CLASS ||
          cpp_id.id_class == cpp_idt::id_classt::TYPEDEF ||
          cpp_id.id_class == cpp_idt::id_classt::SYMBOL,
        "id must be class, typedef, or symbol");

      const symbolt &symb=lookup(cpp_id.identifier);

      // continue if the type is incomplete only
      if(
        cpp_id.id_class == cpp_idt::id_classt::CLASS &&
        (symb.type.id() == ID_struct || symb.type.id() == ID_union))
        return symb;
      else if(cpp_id.id_class == cpp_idt::id_classt::TYPEDEF)
        return symb;
      else if(symb.value.is_not_nil() && symb.type.id() == ID_code)
        return symb;
    }
    else if(
      new_decl.type().id() == ID_struct || new_decl.type().id() == ID_union)
    {
      // The sub-scope lookup may fail when a template is forward-declared
      // in one scope and defined in another (creating different template
      // scopes). Check the symbol table directly for an existing
      // instantiation.
      const irep_idt identifier = id2string(sub_scope.prefix) + "tag-" +
                                  id2string(template_symbol.base_name) + suffix;
      auto s_it = symbol_table.symbols.find(identifier);
      if(
        s_it != symbol_table.symbols.end() &&
        (s_it->second.type.id() == ID_struct ||
         s_it->second.type.id() == ID_union) &&
        !to_struct_union_type(s_it->second.type).is_incomplete())
      {
        return s_it->second;
      }

      // If the symbol exists but is incomplete, the class scope was
      // created under a different (e.g., forward-declaration) template
      // scope that may lack named template parameters. Copy template
      // parameter entries from the current template scope into the
      // class scope so they are visible during elaboration.
      if(s_it != symbol_table.symbols.end())
      {
        auto class_scope_it = cpp_scopes.id_map.find(identifier);
        if(class_scope_it != cpp_scopes.id_map.end())
        {
          cpp_scopet &class_scope =
            static_cast<cpp_scopet &>(*class_scope_it->second);
          for(const auto &param : template_type.template_parameters())
          {
            irep_idt param_base_name;
            if(param.id() == ID_type)
              param_base_name = param.type().get(ID_identifier);
            else
              param_base_name = param.get(ID_identifier);
            if(param_base_name.empty())
              continue;
            const std::string pstr = id2string(param_base_name);
            auto pos = pstr.rfind("::");
            irep_idt base = pos != std::string::npos
                              ? irep_idt(pstr.substr(pos + 2))
                              : param_base_name;
            auto tp_set = template_scope->lookup(
              base,
              cpp_scopet::SCOPE_ONLY,
              cpp_idt::id_classt::TEMPLATE_PARAMETER);
            for(auto *tp : tp_set)
              class_scope.insert(*tp);
          }
        }
      }
    }

    cpp_scopes.go_to(sub_scope);
  }

  // store the information that the template has
  // been instantiated using these arguments
  {
    // need non-const handle on template symbol
    symbolt &s = symbol_table.get_writeable_ref(template_symbol.name);
    irept &instantiated_with = s.value.add(ID_instantiated_with);
    instantiated_with.get_sub().push_back(specialization_template_args);
  }

  #ifdef DEBUG
  std::cout << "CLASS MAP:\n";
  template_map.print(std::cout);
  #endif

  // fix the type
  {
    typet declaration_type=new_decl.type();

    // specialization?
    if(specialization_given)
    {
      if(declaration_type.id()==ID_struct)
      {
        declaration_type=specialization;
        declaration_type.add_source_location()=source_location;
      }
      else
      {
        irept tmp=specialization;
        new_decl.declarators()[0].swap(tmp);
      }
    }

    template_map.apply(declaration_type);
    new_decl.type().swap(declaration_type);

    // Also apply template_map to template parameter defaults.
    // Default arguments like "class = _Templ<_Args...>" contain
    // template parameters that need substitution.
    for(auto &param : new_decl.template_type().template_parameters())
    {
      if(param.has_default_argument())
      {
        exprt &def = static_cast<exprt &>(param.add(ID_C_default_value));
        template_map.apply(def);
        if(def.id() == ID_type)
          template_map.apply(def.type());
      }
    }

    // Expand fold expressions in the class body.
    // Fold expressions like (Bs && ...) reference pack parameters.
    // We expand them into binary expression trees using the actual
    // template arguments.
    if(
      (new_decl.type().id() == ID_struct || new_decl.type().id() == ID_union) &&
      !template_type.template_parameters().empty() &&
      template_type.template_parameters().back().get_bool(ID_ellipsis))
    {
      const auto &pack_param = template_type.template_parameters().back();
      irep_idt pack_base_name;
      if(pack_param.id() == ID_type)
        pack_base_name = pack_param.type().get(ID_identifier);
      else
        pack_base_name = pack_param.get(ID_identifier);

      const std::string pstr = id2string(pack_base_name);
      auto pos = pstr.rfind("::");
      const std::string short_name =
        pos != std::string::npos ? pstr.substr(pos + 2) : pstr;

      const std::size_t non_pack =
        template_type.template_parameters().size() - 1;
      std::vector<exprt> pack_args;
      for(std::size_t k = non_pack; k < full_template_args.arguments().size();
          ++k)
        pack_args.push_back(full_template_args.arguments()[k]);

      auto is_pack_ref = [&short_name](const irept &n) -> bool
      {
        if(n.id() == ID_name)
          return id2string(n.get(ID_identifier)) == short_name;
        if(n.id() == ID_cpp_name && !n.get_sub().empty())
        {
          const auto &front = n.get_sub().front();
          if(front.id() == ID_name)
            return id2string(front.get(ID_identifier)) == short_name;
        }
        return false;
      };

      std::function<bool(const irept &)> contains_pack_ref;
      contains_pack_ref = [&is_pack_ref,
                           &contains_pack_ref](const irept &n) -> bool
      {
        if(is_pack_ref(n))
          return true;
        for(const auto &s : n.get_sub())
          if(contains_pack_ref(s))
            return true;
        for(const auto &ns : n.get_named_sub())
          if(contains_pack_ref(ns.second))
            return true;
        return false;
      };

      std::function<irept(const irept &, const exprt &)> substitute_arg;
      substitute_arg = [&is_pack_ref, &substitute_arg](
                         const irept &n, const exprt &arg) -> irept
      {
        if(is_pack_ref(n))
          return arg;
        irept result = n;
        for(auto &s : result.get_sub())
          s = substitute_arg(s, arg);
        return result;
      };

      std::function<void(irept &)> expand_folds;
      expand_folds = [&](irept &node)
      {
        if(
          (node.id() == irep_idt("cpp_right_fold") ||
           node.id() == irep_idt("cpp_left_fold")) &&
          !node.get_sub().empty() && contains_pack_ref(node.get_sub().front()))
        {
          const irep_idt fold_op = node.get(irep_idt("fold_op"));
          const irept &pack_expr = node.get_sub().front();
          bool is_left = (node.id() == irep_idt("cpp_left_fold"));

          if(pack_args.empty())
          {
            if(fold_op == ID_and)
              node = true_exprt();
            else if(fold_op == ID_or)
              node = false_exprt();
            else
              node = from_integer(0, signed_int_type());
            return;
          }

          if(pack_args.size() == 1)
          {
            node = substitute_arg(pack_expr, pack_args[0]);
            return;
          }

          if(is_left)
          {
            irept result = substitute_arg(pack_expr, pack_args[0]);
            for(std::size_t i = 1; i < pack_args.size(); ++i)
            {
              irept bin(fold_op);
              bin.get_sub().push_back(result);
              bin.get_sub().push_back(substitute_arg(pack_expr, pack_args[i]));
              result = bin;
            }
            node = result;
          }
          else
          {
            irept result =
              substitute_arg(pack_expr, pack_args[pack_args.size() - 1]);
            for(int i = static_cast<int>(pack_args.size()) - 2; i >= 0; --i)
            {
              irept bin(fold_op);
              bin.get_sub().push_back(substitute_arg(pack_expr, pack_args[i]));
              bin.get_sub().push_back(result);
              result = bin;
            }
            node = result;
          }
          return;
        }

        for(auto &s : node.get_sub())
          expand_folds(s);
        for(auto &ns : node.get_named_sub())
          expand_folds(ns.second);
      };

      irept &body = new_decl.type().add(ID_body);
      expand_folds(body);
    }

    // Expand variadic base classes: Bases... → Base0, Base1, ...
    if(
      new_decl.type().id() == ID_struct &&
      !template_type.template_parameters().empty() &&
      template_type.template_parameters().back().get_bool(ID_ellipsis))
    {
      irept &bases_irep = new_decl.type().add(ID_bases);
      irept::subt &bases_sub = bases_irep.get_sub();
      irept::subt expanded_bases;
      const std::size_t non_pack =
        template_type.template_parameters().size() - 1;

      for(auto &base : bases_sub)
      {
        // Check if this base references the pack parameter
        const irept &base_name = base.find(ID_name);
        bool is_pack_base = false;
        if(base_name.id() == ID_cpp_name)
        {
          for(const auto &sub : base_name.get_sub())
          {
            if(sub.id() == ID_name)
            {
              // Check if this name matches the pack parameter
              const auto &pack_param =
                template_type.template_parameters().back();
              const std::string full_id =
                id2string(pack_param.type().get(ID_identifier));
              auto pos = full_id.rfind("::");
              const std::string pack_name =
                pos != std::string::npos ? full_id.substr(pos + 2) : full_id;
              if(id2string(sub.get(ID_identifier)) == pack_name)
                is_pack_base = true;
              break;
            }
          }
        }

        if(is_pack_base)
        {
          // Expand: create one base for each pack argument
          for(std::size_t k = non_pack;
              k < full_template_args.arguments().size();
              ++k)
          {
            const exprt &arg = full_template_args.arguments()[k];
            if(arg.id() == ID_type)
            {
              irept new_base = base;
              // Replace the name with the concrete type
              const std::string tag_id =
                id2string(arg.type().get(ID_identifier));
              // Strip "tag-" prefix to get the class name
              std::string class_name = tag_id;
              if(class_name.substr(0, 4) == "tag-")
                class_name = class_name.substr(4);
              irept new_name(ID_cpp_name);
              irept name_sub(ID_name);
              name_sub.set(ID_identifier, class_name);
              new_name.get_sub().push_back(name_sub);
              new_base.add(ID_name) = new_name;
              expanded_bases.push_back(new_base);
            }
          }
        }
        else
        {
          expanded_bases.push_back(base);
        }
      }
      bases_sub = expanded_bases;
    }

    // Also apply template map to declarator types (function parameters)
    for(auto &d : new_decl.declarators())
      template_map.apply(d.type());
  }

  if(new_decl.type().id() == ID_struct || new_decl.type().id() == ID_union)
  {
    // Before instantiating from the primary template, check if there is
    // a full specialization (template<>) that matches the template
    // arguments. If so, use the specialization instead.
    if(
      !specialization_given &&
      template_symbol.type.get(ID_specialization_of).empty())
    {
      cpp_scopet &parent_scope = template_scope->get_parent();
      cpp_scopet::id_sett id_set =
        parent_scope.lookup(template_symbol.base_name, cpp_scopet::SCOPE_ONLY);

      for(const auto *id_ptr : id_set)
      {
        const symbolt &s = lookup(id_ptr->identifier);
        if(s.type.get(ID_specialization_of).empty())
          continue;

        const cpp_declarationt &spec_decl = to_cpp_declaration(s.type);
        // Only consider full specializations (zero template parameters)
        if(!spec_decl.template_type().template_parameters().empty())
          continue;

        const cpp_template_args_non_tct &spec_args =
          spec_decl.partial_specialization_args();
        if(
          spec_args.arguments().size() != full_template_args.arguments().size())
        {
          continue;
        }

        // Typecheck the specialization args and compare
        cpp_saved_template_mapt saved_map2(template_map);
        cpp_save_scopet save_scope2(cpp_scopes);
        cpp_template_args_tct spec_args_tc;
        bool match = false;
        try
        {
          spec_args_tc = typecheck_template_args(
            source_location, template_symbol, spec_args);
          match = (spec_args_tc.arguments() == full_template_args.arguments());
        }
        catch(...)
        {
        }

        if(match)
        {
          // Re-instantiate using the full specialization
          return instantiate_template(
            source_location, s, spec_args_tc, full_template_args);
        }
      }
    }

    // Switch to the sub-scope so that typecheck_compound_type creates
    // the class symbol with an identifier that includes the template
    // suffix, matching the identifier used by class_template_symbol.
    cpp_scopes.go_to(sub_scope);

    // a class template
    // Apply template map to static member initializers in the class
    // body to substitute non-type template parameters before processing.
    if(new_decl.type().id() == ID_struct || new_decl.type().id() == ID_union)
    {
      irept &body = new_decl.type().add(ID_body);
      for(auto &member : body.get_sub())
      {
        if(member.id() != ID_cpp_declaration)
          continue;
        for(auto &sub : member.get_sub())
        {
          if(sub.id() == ID_cpp_declarator)
          {
            exprt &val = static_cast<exprt &>(sub.add(ID_value));
            if(val.is_not_nil())
              template_map.apply(val);
          }
        }
      }
    }
    // Per [temp.variadic]/5: remove empty pack expansions
    if(
      id2string(template_symbol.name).find("_Compressed_pair") !=
        std::string::npos &&
      id2string(template_symbol.name).find("_Zero") != std::string::npos)
    {
      if(!template_map.pack_size_map.empty() && !new_decl.declarators().empty())
      {
        std::set<std::string> ep_names;
        for(const auto &ps : template_map.pack_size_map)
        {
          if(ps.second == 0)
          {
            const std::string full = id2string(ps.first);
            auto pos = full.rfind("::");
            ep_names.insert(
              pos != std::string::npos ? full.substr(pos + 2) : full);
          }
        }
        if(!ep_names.empty())
        {
          auto &dt = new_decl.declarators()[0].type();
          if(dt.id() == ID_function_type)
          {
            irept &params = dt.add(ID_parameters);
            params.get_sub().erase(
              std::remove_if(
                params.get_sub().begin(),
                params.get_sub().end(),
                [](const irept &p)
                {
                  if(p.id() != ID_cpp_declaration)
                    return false;
                  for(const auto &d : p.get_sub())
                    if(
                      d.id() == ID_cpp_declarator &&
                      (d.find(ID_type).get_bool(ID_ellipsis) ||
                       d.get_bool(ID_ellipsis)))
                      return true;
                  return false;
                }),
              params.get_sub().end());
          }
          // Per [temp.variadic]/7: remove pack expansion expressions.
          // After template_map.apply(), pack params may appear as
          // template_parameter_symbol_typet or as ID_name nodes.
          std::function<bool(const irept &)> has_ep =
            [&](const irept &n) -> bool
          {
            if(
              n.id() == ID_name &&
              ep_names.count(id2string(n.get(ID_identifier))))
              return true;
            // Check template_parameter_symbol_typet
            if(n.id() == ID_template_parameter_symbol_type)
            {
              const std::string full = id2string(n.get(ID_identifier));
              auto pos = full.rfind("::");
              const std::string sn =
                pos != std::string::npos ? full.substr(pos + 2) : full;
              if(ep_names.count(sn))
                return true;
            }
            // Check type sub for template_parameter_symbol_typet
            const auto &type_sub = n.find(ID_type);
            if(
              type_sub.is_not_nil() &&
              type_sub.id() == ID_template_parameter_symbol_type)
            {
              const std::string full = id2string(type_sub.get(ID_identifier));
              auto pos = full.rfind("::");
              const std::string sn =
                pos != std::string::npos ? full.substr(pos + 2) : full;
              if(ep_names.count(sn))
                return true;
            }
            for(const auto &s : n.get_sub())
              if(has_ep(s))
                return true;
            for(const auto &ns : n.get_named_sub())
              if(has_ep(ns.second))
                return true;
            return false;
          };
          irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
          for(auto &init : mi.get_sub())
          {
            auto &subs = init.get_sub();
            subs.erase(
              std::remove_if(
                subs.begin(),
                subs.end(),
                [&](const irept &s) { return has_ep(s); }),
              subs.end());
          }
        }
      }
    }

    convert_non_template_declaration(new_decl);

    // Propagate template info to the class symbol so that member
    // function template bodies can find the class template parameters.
    {
      std::string inst_suffix = template_suffix(full_template_args);
      irep_idt class_sym_id = id2string(sub_scope.prefix) + "tag-" +
                              id2string(template_symbol.base_name) +
                              inst_suffix;
      if(auto *cs = symbol_table.get_writeable(class_sym_id))
      {
        if(cs->type.find(ID_C_template).is_nil())
        {
          cs->type.set(
            ID_C_template,
            to_cpp_declaration(template_symbol.type).template_type());
          cs->type.set(ID_C_template_arguments, specialization_template_args);
        }
      }
    }

    // Restore the template scope for template method processing.
    saved_scope.restore();
    cpp_scopes.go_to(*template_scope);

    // also instantiate all the template methods
    const exprt &template_methods = static_cast<const exprt &>(
      template_symbol.value.find(ID_template_methods));

    for(auto &tm : template_methods.operands())
    {
      saved_scope.restore();

      cpp_declarationt method_decl=
        static_cast<const cpp_declarationt &>(
          static_cast<const irept &>(tm));

      // Member class/union templates are already instantiated as part
      // of the class body by convert_non_template_declaration above.
      if(method_decl.is_class_template())
        continue;

      // Member template aliases (e.g., template<typename U> using X = ...)
      // are already handled during class body conversion. Skip them here
      // to avoid resolving their template parameters in the wrong scope.
      if(method_decl.is_template_alias())
      {
        continue;
      }

      // copy the type of the template method
      template_typet method_type=
        method_decl.template_type();

      // If this method has more template parameters than the class
      // template, it is a member function template (e.g.,
      // template<T> template<U> void S<T>::f(U x) {}).
      // Skip it during class instantiation — it will be instantiated
      // when actually called.
      // Also skip methods with fewer template parameters — these belong
      // to a partial specialization (e.g., vector<bool, _Alloc> has 1
      // parameter vs the primary vector<T, _Alloc> with 2).
      const std::size_t n_class_params =
        specialization_template_args.arguments().size();
      const std::size_t n_method_params =
        method_type.template_parameters().size();

      if(n_method_params != n_class_params)
      {
        // Member function template — register in the instantiated
        // class scope so operator overload resolution can find it.
        if(!method_decl.declarators().empty())
        {
          const irep_idt &base_name =
            method_decl.declarators().front().name().get_base_name();
          if(!base_name.empty())
          {
            std::string inst_suffix = template_suffix(full_template_args);
            irep_idt class_id = id2string(sub_scope.prefix) + "tag-" +
                                id2string(template_symbol.base_name) +
                                inst_suffix;
            auto it = cpp_scopes.id_map.find(class_id);
            if(it != cpp_scopes.id_map.end())
            {
              // Find the template symbol in the original class scope
              // Search the template scope and its immediate children
              // (the class body scope) for the member function template.
              auto tmpl_results = template_scope->lookup(
                base_name,
                cpp_scopet::SCOPE_ONLY,
                cpp_idt::id_classt::TEMPLATE);
              if(tmpl_results.empty())
              {
                // Search children (class body scope)
                tmpl_results = template_scope->lookup(
                  base_name,
                  cpp_scopet::QUALIFIED,
                  cpp_idt::id_classt::TEMPLATE);
              }
              for(auto *tmpl_id : tmpl_results)
              {
                auto &cs = static_cast<cpp_scopet &>(*it->second);
                cpp_idt &new_id = cs.insert(base_name);
                new_id.id_class = cpp_idt::id_classt::TEMPLATE;
                new_id.identifier = tmpl_id->identifier;
                new_id.is_member = true;
                break;
              }
            }
          }
        }
        continue;
      }

      // Skip methods whose class qualifier contains concrete template
      // arguments that don't match the current instantiation. This
      // filters out methods of partial specializations (e.g.,
      // vector<bool, _Alloc>::_M_insert_range) when instantiating the
      // primary template (e.g., vector<unsigned int, allocator<...>>).
      if(!method_decl.declarators().empty())
      {
        const auto &name = method_decl.declarators().front().name();
        bool skip = false;
        for(const auto &sub : name.get_sub())
        {
          if(sub.id() != ID_template_args)
            continue;
          const auto &targs = sub.find(ID_arguments).get_sub();
          for(std::size_t i = 0;
              i < targs.size() && i < full_template_args.arguments().size();
              i++)
          {
            // Template arguments that are template parameter names
            // (cpp_name) are not concrete — skip those.
            const irept *t = &targs[i];
            if(t->id() == ID_type)
              t = &t->find(ID_type);
            if(t->id() == ID_ambiguous)
              t = &t->find(ID_type);
            if(t->id() == ID_cpp_name || t->id() == ID_nil || t->id().empty())
              continue;
            // This is a concrete type. Convert and compare.
            const auto &full_arg = full_template_args.arguments()[i];
            if(full_arg.id() != ID_type)
              continue;
            typet concrete = static_cast<const typet &>(*t);
            try
            {
              cpp_convert_plain_type(concrete, get_message_handler());
            }
            catch(...)
            {
              continue;
            }
            if(concrete != full_arg.type())
            {
              skip = true;
              break;
            }
          }
          break;
        }
        if(skip)
          continue;
      }

      // do template parameters
      // this also sets up the template scope of the method
      cpp_scopet &method_scope=
        typecheck_template_parameters(method_type);

      cpp_scopes.go_to(method_scope);

      // mapping from template arguments to values/types
      template_map.build(method_type, specialization_template_args);
#ifdef DEBUG
      std::cout << "METHOD MAP:\n";
      template_map.print(std::cout);
#endif

      method_decl.remove(ID_template_type);
      method_decl.remove(ID_is_template);

      // Apply the template map to substitute template parameters
      // (e.g. _Dom, _Tp) with the actual types in the method
      // declaration before converting it.
      // First, type-check the declaration type in the method's
      // template scope so that template parameter names (cpp_name)
      // are resolved to template_parameter_symbol_type, then apply
      // the template map to replace them with actual types.
      // Add the class scope as a using scope so that class-scoped
      // names (e.g., typedefs like 'iterator' in trailing return
      // types) can also be resolved.
      if(method_decl.type().id() == ID_cpp_name)
      {
        const irep_idt &inst_class_name = new_decl.type().get(ID_identifier);
        if(!inst_class_name.empty())
        {
          cpp_scopet &class_scope = cpp_scopes.get_scope(inst_class_name);
          method_scope.add_using_scope(class_scope);
        }
        typecheck_type(method_decl.type());
        template_map.apply(method_decl.type());
      }

      convert(method_decl);
    }

    const irep_idt& new_symb_id = new_decl.type().get(ID_identifier);

    // Move deferred methods of this class to method_bodies.
    // Methods are added to deferred_typechecking during class body
    // processing because the parent scope is a template scope.
    {
      std::string class_name = id2string(new_symb_id);
      if(class_name.substr(0, 4) == "tag-")
        class_name = class_name.substr(4);
      class_name += "::";
      std::vector<irep_idt> to_move;
      for(const auto &d : deferred_typechecking)
      {
        if(id2string(d).find(class_name) != std::string::npos)
          to_move.push_back(d);
      }
      for(const auto &d : to_move)
      {
        deferred_typechecking.erase(d);
        auto *sym = symbol_table.get_writeable(d);
        if(!sym)
          continue;

        // If the method has nil body, check if a body is available
        // from template_methods (out-of-class definitions in .tcc).
        // Search ALL template symbols, not just the current one.
        if(sym->value.is_nil() && sym->type.id() == ID_code)
        {
          for(const auto &tsp : symbol_table)
          {
            if(!tsp.second.type.get_bool(ID_is_template))
              continue;
            if(tsp.second.value.is_nil())
              continue;
            const exprt &tms = static_cast<const exprt &>(
              tsp.second.value.find(ID_template_methods));
            for(const auto &tm : tms.operands())
            {
              const cpp_declarationt &md =
                static_cast<const cpp_declarationt &>(
                  static_cast<const irept &>(tm));
              if(md.declarators().empty())
                continue;
              if(md.declarators()[0].name().get_base_name() != sym->base_name)
                continue;
              if(md.declarators()[0].find(ID_value).is_nil())
                continue;
              // Found body. Apply class template substitution.
              const template_typet &md_tt = md.template_type();
              std::size_t n_md = md_tt.template_parameters().size();
              std::size_t n_cls =
                specialization_template_args.arguments().size();
              if(n_md <= n_cls)
              {
                // Regular method: substitute all params
                exprt body = static_cast<const exprt &>(
                  md.declarators()[0].find(ID_value));
                cpp_saved_template_mapt sm(template_map);
                template_map.build(md_tt, specialization_template_args);
                template_map.apply(body);
                // Per [temp.variadic]/7: remove empty pack
                // expansion expressions from the body.
                if(!template_map.pack_size_map.empty())
                {
                  std::set<std::string> ep;
                  for(const auto &ps : template_map.pack_size_map)
                    if(ps.second == 0)
                    {
                      const std::string f = id2string(ps.first);
                      auto p = f.rfind("::");
                      ep.insert(p != std::string::npos ? f.substr(p + 2) : f);
                    }
                  if(!ep.empty())
                  {
                    std::function<bool(const irept &)> has_ep =
                      [&](const irept &n) -> bool
                    {
                      if(n.id() == ID_template_parameter_symbol_type)
                      {
                        const std::string f = id2string(n.get(ID_identifier));
                        auto p = f.rfind("::");
                        if(ep.count(
                             p != std::string::npos ? f.substr(p + 2) : f))
                          return true;
                      }
                      if(
                        n.id() == ID_name &&
                        ep.count(id2string(n.get(ID_identifier))))
                        return true;
                      for(const auto &s : n.get_sub())
                        if(has_ep(s))
                          return true;
                      for(const auto &ns : n.get_named_sub())
                        if(has_ep(ns.second))
                          return true;
                      return false;
                    };
                    // Remove from member_initializers in body
                    irept &mi = body.add(ID_member_initializers);
                    for(auto &init : mi.get_sub())
                    {
                      auto &subs = init.get_sub();
                      subs.erase(
                        std::remove_if(
                          subs.begin(),
                          subs.end(),
                          [&](const irept &s) { return has_ep(s); }),
                        subs.end());
                    }
                  }
                }
                sym->value = body;
              }
              else
              {
                // Member function template: substitute class params,
                // deduce method params from concrete function sig.
                exprt body = static_cast<const exprt &>(
                  md.declarators()[0].find(ID_value));
                // Build full args: class args + deduced method args
                cpp_template_args_tct full;
                for(const auto &a : specialization_template_args.arguments())
                  full.arguments().push_back(a);
                // Deduce method params from function signature
                const code_typet &cft = to_code_type(sym->type);
                const auto &cps = cft.parameters();
                std::size_t off = (!cps.empty() && cps[0].get_this()) ? 1 : 0;
                for(std::size_t i = n_cls; i < n_md; i++)
                {
                  exprt a(ID_type);
                  if(off < cps.size())
                    a.type() = cps[off].type();
                  else
                    a.type() = typet(ID_empty);
                  full.arguments().push_back(a);
                }
                cpp_saved_template_mapt sm(template_map);
                template_map.build(md_tt, full);
                template_map.apply(body);
                // Per [temp.variadic]/7: remove empty pack
                // expansion expressions from the body.
                if(!template_map.pack_size_map.empty())
                {
                  std::set<std::string> ep;
                  for(const auto &ps : template_map.pack_size_map)
                    if(ps.second == 0)
                    {
                      const std::string f = id2string(ps.first);
                      auto p = f.rfind("::");
                      ep.insert(p != std::string::npos ? f.substr(p + 2) : f);
                    }
                  if(!ep.empty())
                  {
                    std::function<bool(const irept &)> has_ep =
                      [&](const irept &n) -> bool
                    {
                      if(n.id() == ID_template_parameter_symbol_type)
                      {
                        const std::string f = id2string(n.get(ID_identifier));
                        auto p = f.rfind("::");
                        if(ep.count(
                             p != std::string::npos ? f.substr(p + 2) : f))
                          return true;
                      }
                      if(
                        n.id() == ID_name &&
                        ep.count(id2string(n.get(ID_identifier))))
                        return true;
                      for(const auto &s : n.get_sub())
                        if(has_ep(s))
                          return true;
                      for(const auto &ns : n.get_named_sub())
                        if(has_ep(ns.second))
                          return true;
                      return false;
                    };
                    // Remove from member_initializers in body
                    irept &mi = body.add(ID_member_initializers);
                    for(auto &init : mi.get_sub())
                    {
                      auto &subs = init.get_sub();
                      subs.erase(
                        std::remove_if(
                          subs.begin(),
                          subs.end(),
                          [&](const irept &s) { return has_ep(s); }),
                        subs.end());
                    }
                  }
                }
                // Also copy member initializers into the body
                // so the method body pass can process them.
                // Remove empty pack expressions per [temp.variadic]/7.
                const irept &mi_src =
                  md.declarators()[0].find(ID_member_initializers);
                if(mi_src.is_not_nil())
                {
                  irept mi_copy = mi_src;
                  if(!template_map.pack_size_map.empty())
                  {
                    std::set<std::string> ep2;
                    for(const auto &ps : template_map.pack_size_map)
                      if(ps.second == 0)
                      {
                        const std::string f = id2string(ps.first);
                        auto p = f.rfind("::");
                        ep2.insert(
                          p != std::string::npos ? f.substr(p + 2) : f);
                      }
                    if(!ep2.empty())
                    {
                      std::function<bool(const irept &)> has_ep2 =
                        [&](const irept &n) -> bool
                      {
                        if(n.id() == ID_template_parameter_symbol_type)
                        {
                          const std::string f = id2string(n.get(ID_identifier));
                          auto p = f.rfind("::");
                          if(ep2.count(
                               p != std::string::npos ? f.substr(p + 2) : f))
                            return true;
                        }
                        if(
                          n.id() == ID_name &&
                          ep2.count(id2string(n.get(ID_identifier))))
                          return true;
                        for(const auto &s : n.get_sub())
                          if(has_ep2(s))
                            return true;
                        for(const auto &ns : n.get_named_sub())
                          if(has_ep2(ns.second))
                            return true;
                        return false;
                      };
                      for(auto &init : mi_copy.get_sub())
                      {
                        auto &subs = init.get_sub();
                        subs.erase(
                          std::remove_if(
                            subs.begin(),
                            subs.end(),
                            [&](const irept &s) { return has_ep2(s); }),
                          subs.end());
                      }
                    }
                  }
                  body.add(ID_member_initializers) = mi_copy;
                }
                sym->value = body;
              }
              goto body_found;
            }
          }
        body_found:
        {
        }
        }

        add_method_body(sym);
      }
    }

    symbolt &new_symb = symbol_table.get_writeable_ref(new_symb_id);

    // add template arguments to type in order to retrieve template map when
    // typechecking function body
    new_symb.type.set(ID_C_template, template_type);
    new_symb.type.set(ID_C_template_arguments, specialization_template_args);

#ifdef DEBUG
    std::cout << "instance symbol: " << new_symb.name << "\n\n";
    std::cout << "template type: " << template_type.pretty() << "\n\n";
#endif

    return new_symb;
  }

  if(is_template_method && !new_decl.is_typedef())
  {
    // Apply template_map to parameter types for SFINAE substitution
    for(auto &d : new_decl.declarators())
      template_map.apply(d.type());
    symbolt &symb = symbol_table.get_writeable_ref(class_name);

    if(new_decl.declarators().size() != 1)
    {
      error().source_location = source_location;
      error() << "expected exactly one declarator in template" << eom;
      throw 0;
    }

    if(new_decl.member_spec().is_virtual())
    {
      error().source_location=new_decl.source_location();
      error() << "invalid use of `virtual' in template declaration"
              << eom;
      throw 0;
    }

    if(
      new_decl.storage_spec().is_extern() ||
      new_decl.storage_spec().is_register() ||
      new_decl.storage_spec().is_mutable())
    {
      error().source_location=new_decl.source_location();
      error() << "invalid storage class specified for template field" << eom;
      throw 0;
    }

    // In C++11, 'auto' in a template member declaration indicates a
    // trailing return type. Only reject it when there are no declarators.
    if(new_decl.storage_spec().is_auto() && new_decl.declarators().empty())
    {
      error().source_location = new_decl.source_location();
      error() << "invalid storage class specified for template field" << eom;
      throw 0;
    }

    bool is_static=new_decl.storage_spec().is_static();
    irep_idt access = new_decl.get(ID_C_access);

    CHECK_RETURN(!access.empty());
    PRECONDITION(symb.type.id() == ID_struct || symb.type.id() == ID_union);

    // If the method declaration has no body, check if the body was
    // provided by an out-of-class definition (stored in template_methods
    // of the class template).
    if(new_decl.declarators()[0].find(ID_value).is_nil())
    {
      // Find the class template symbol
      for(const auto &sp : symbol_table)
      {
        if(
          sp.second.type.get_bool(ID_is_template) &&
          sp.second.value.is_not_nil())
        {
          // Match by base name OR by checking if this template's
          // instantiated_with includes the current class.
          if(sp.second.base_name != symb.base_name)
            continue;
          const exprt &tmethods = static_cast<const exprt &>(
            sp.second.value.find(ID_template_methods));
          if(tmethods.operands().empty())
            continue;
          irep_idt method_base =
            new_decl.declarators()[0].name().get_base_name();
          for(const auto &tm : tmethods.operands())
          {
            const cpp_declarationt &md = static_cast<const cpp_declarationt &>(
              static_cast<const irept &>(tm));
            if(md.declarators().empty())
              continue;
            if(md.declarators()[0].name().get_base_name() != method_base)
              continue;
            if(md.declarators()[0].find(ID_value).is_nil())
              continue;
            // Verify this is a member function template
            const template_typet &md_tt = md.template_type();
            if(
              md_tt.template_parameters().size() <=
              specialization_template_args.arguments().size())
              continue;
            // Copy the body. The body is in parsed (not type-checked)
            // form. It will be type-checked by typecheck_method_bodies
            // with the proper template map.
            new_decl.declarators()[0].add(ID_value) =
              md.declarators()[0].find(ID_value);
            goto body_found_is_tm;
          }
          continue;
        }
      }
    body_found_is_tm:
    {
    }
    }

    // Per [temp.variadic]/5: set pack_size_map and remove empty
    // pack expansions for function template members.
    if(new_decl.is_template())
    {
      const auto &fn_params = new_decl.template_type().template_parameters();
      for(const auto &p : fn_params)
      {
        if(p.get_bool(ID_ellipsis))
        {
          irep_idt pid = p.type().get(ID_identifier);
          if(
            !pid.empty() &&
            template_map.type_map.find(pid) == template_map.type_map.end())
            template_map.pack_size_map[pid] = 0;
        }
      }
      if(!template_map.pack_size_map.empty() && !new_decl.declarators().empty())
      {
        std::set<std::string> ep_names;
        for(const auto &ps : template_map.pack_size_map)
          if(ps.second == 0)
          {
            const std::string f = id2string(ps.first);
            auto p = f.rfind("::");
            ep_names.insert(p != std::string::npos ? f.substr(p + 2) : f);
          }
        if(!ep_names.empty())
        {
          // Remove pack params from function type
          auto &dt = new_decl.declarators()[0].type();
          if(dt.id() == ID_function_type)
          {
            irept &params = dt.add(ID_parameters);
            params.get_sub().erase(
              std::remove_if(
                params.get_sub().begin(),
                params.get_sub().end(),
                [&](const irept &p)
                {
                  if(p.id() != ID_cpp_declaration)
                    return false;
                  for(const auto &d : p.get_sub())
                  {
                    if(
                      d.id() == ID_cpp_declarator &&
                      (d.find(ID_type).get_bool(ID_ellipsis) ||
                       d.get_bool(ID_ellipsis)))
                      return true;
                    // Also check for template_parameter_symbol_typet
                    // referencing empty pack
                    const auto &dtype = d.find(ID_type);
                    if(dtype.id() == ID_template_parameter_symbol_type)
                    {
                      const std::string f = id2string(dtype.get(ID_identifier));
                      auto pos = f.rfind("::");
                      if(ep_names.count(
                           pos != std::string::npos ? f.substr(pos + 2) : f))
                        return true;
                    }
                  }
                  // Check the type sub of the declaration
                  const auto &ptype = p.find(ID_type);
                  if(ptype.id() == ID_template_parameter_symbol_type)
                  {
                    const std::string f = id2string(ptype.get(ID_identifier));
                    auto pos = f.rfind("::");
                    if(ep_names.count(
                         pos != std::string::npos ? f.substr(pos + 2) : f))
                      return true;
                  }
                  return false;
                }),
              params.get_sub().end());
          }
          // Remove member initializer expressions with empty pack
          std::function<bool(const irept &)> has_ep =
            [&](const irept &n) -> bool
          {
            if(n.id() == ID_template_parameter_symbol_type)
            {
              const std::string f = id2string(n.get(ID_identifier));
              auto p = f.rfind("::");
              if(ep_names.count(p != std::string::npos ? f.substr(p + 2) : f))
                return true;
            }
            if(
              n.id() == ID_name &&
              ep_names.count(id2string(n.get(ID_identifier))))
              return true;
            const auto &tsub = n.find(ID_type);
            if(tsub.is_not_nil() && has_ep(tsub))
              return true;
            for(const auto &s : n.get_sub())
              if(has_ep(s))
                return true;
            for(const auto &ns : n.get_named_sub())
              if(ns.first != ID_type && has_ep(ns.second))
                return true;
            return false;
          };
          irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
          for(auto &init : mi.get_sub())
          {
            auto &subs = init.get_sub();
            subs.erase(
              std::remove_if(
                subs.begin(),
                subs.end(),
                [&](const irept &s) { return has_ep(s); }),
              subs.end());
          }
        }
      }
      // Per [temp.variadic]/7: for non-empty packs, substitute
      // pack parameter names with actual types.
      if(!template_map.pack_args_map.empty() && !new_decl.declarators().empty())
      {
        std::map<std::string, irep_idt> pack_subst;
        for(const auto &pa : template_map.pack_args_map)
        {
          if(pa.second.empty())
            continue;
          const std::string full = id2string(pa.first);
          auto p = full.rfind("::");
          const std::string sn =
            p != std::string::npos ? full.substr(p + 2) : full;
          const typet &t = pa.second.front();
          if(t.id() == ID_struct_tag)
          {
            std::string tag = id2string(to_struct_tag_type(t).get_identifier());
            if(tag.substr(0, 4) == "tag-")
              tag = tag.substr(4);
            pack_subst[sn] = tag;
          }
        }
        if(!pack_subst.empty())
        {
          std::function<void(irept &)> subst = [&](irept &node)
          {
            if(
              node.id() == ID_name &&
              pack_subst.count(id2string(node.get(ID_identifier))))
              node.set(
                ID_identifier,
                pack_subst.at(id2string(node.get(ID_identifier))));
            for(auto &s : node.get_sub())
              subst(s);
            for(auto &ns : node.get_named_sub())
              subst(ns.second);
          };
          irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
          subst(mi);
        }
      }
      // Per [temp.variadic]/7: for non-empty packs, substitute
      // pack parameter names with actual types.
      if(!template_map.pack_args_map.empty() && !new_decl.declarators().empty())
      {
        std::map<std::string, irep_idt> pack_subst;
        for(const auto &pa : template_map.pack_args_map)
        {
          if(pa.second.empty())
            continue;
          const std::string full = id2string(pa.first);
          auto p = full.rfind("::");
          const std::string sn =
            p != std::string::npos ? full.substr(p + 2) : full;
          const typet &t = pa.second.front();
          if(t.id() == ID_struct_tag)
          {
            std::string tag = id2string(to_struct_tag_type(t).get_identifier());
            if(tag.substr(0, 4) == "tag-")
              tag = tag.substr(4);
            auto tag_pos = tag.find("tag-");
            if(tag_pos != std::string::npos)
              tag = tag.substr(0, tag_pos) + tag.substr(tag_pos + 4);
            auto last_sep = tag.rfind("::");
            if(last_sep != std::string::npos)
              tag = tag.substr(last_sep + 2);
            pack_subst[sn] = tag;
          }
        }
        if(!pack_subst.empty())
        {
          std::function<void(irept &)> subst = [&](irept &node)
          {
            if(
              node.id() == ID_name &&
              pack_subst.count(id2string(node.get(ID_identifier))))
              node.set(
                ID_identifier,
                pack_subst.at(id2string(node.get(ID_identifier))));
            node.remove(ID_ellipsis);
            for(auto &s : node.get_sub())
              subst(s);
            for(auto &ns : node.get_named_sub())
              subst(ns.second);
          };
          irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
          subst(mi);
        }
      }
    }

    // Per [temp.inst]/3: member function template type-checking
    // may fail when function template parameters are not in the
    // class template map.  Catch and return the template symbol.
    {
      // [temp.inst]/2 + [temp.deduct]/8: substituting and type-
      // checking a compound member declaration during template
      // instantiation is a SFINAE immediate context — a failure
      // here doesn't invalidate the template specialization, it
      // just means we can't complete this member and bail out to
      // the caller with the template symbol.
      try
      {
        sfinae_contextt sfinae_guard{*this};
        typecheck_compound_declarator(
          symb,
          new_decl,
          new_decl.declarators()[0],
          to_struct_union_type(symb.type).components(),
          access,
          is_static,
          false,
          false);
      }
      catch(...)
      {
        return template_symbol;
      }
    }

    const symbolt &method_sym =
      lookup(to_struct_type(symb.type).components().back().get_name());

    // The method was added to deferred_typechecking by
    // typecheck_compound_declarator (because the parent scope is a template
    // scope). Since we are actually instantiating this method, move it
    // from deferred_typechecking to method_bodies so the body gets
    // type-checked and is not erased during clean_up.
    if(deferred_typechecking.erase(method_sym.name))
    {
      symbolt &ws = symbol_table.get_writeable_ref(method_sym.name);
      // Per [temp.inst]/1: store function template parameters and
      // arguments so method_bodies can restore the template_map.
      ws.type.add(irep_idt{"#fn_template_type"}) = template_type;
      ws.type.add(irep_idt{"#fn_template_args"}) = specialization_template_args;
      add_method_body(&ws);
    }

    return method_sym;
  }

  // not a class template, not a class template method,
  // it must be a function template, a template alias, or a variable template!

  if(new_decl.declarators().size() != 1)
  {
    error().source_location = source_location;
    error() << "expected exactly one declarator in template" << eom;
    throw 0;
  }

  // Variable template: the declarator type is not a function type.
  // Instantiate by converting the declaration directly.
  if(
    !new_decl.declarators().empty() &&
    new_decl.declarators()[0].type().id() != ID_function_type &&
    new_decl.type().id() != ID_struct && new_decl.type().id() != ID_union &&
    !new_decl.is_typedef())
  {
    // Check for a better-matching partial specialization.
    if(template_symbol.type.get(ID_specialization_of).empty())
    {
      // Resolve symbol references in full_template_args so that
      // expressions like "x % y" (where x, y are const symbols)
      // are simplified to constants for matching.
      cpp_template_args_tct full_args_resolved = full_template_args;
      for(auto &arg : full_args_resolved.arguments())
      {
        if(arg.id() == ID_type)
          continue;
        for(int pass = 0; pass < 10; ++pass)
        {
          bool changed = false;
          arg.visit_pre(
            [this, &changed](exprt &node)
            {
              if(node.id() == ID_symbol)
              {
                const symbolt &sym =
                  lookup(to_symbol_expr(node).get_identifier());
                if(sym.value.is_not_nil() && cpp_is_pod(sym.type))
                {
                  node = sym.value;
                  changed = true;
                }
              }
            });
          if(!changed)
            break;
          simplify(arg, *this);
          if(arg.is_constant())
            break;
        }
      }

      cpp_scopet *ts = id_map_lookup(cpp_scopes, template_symbol.name);
      if(ts != nullptr)
      {
        cpp_scopet &parent_scope = ts->get_parent();
        cpp_scopet::id_sett id_set = parent_scope.lookup(
          template_symbol.base_name, cpp_scopet::SCOPE_ONLY);

        const symbolt *best_match = nullptr;
        cpp_template_args_tct best_spec_args;

        // [temp.deduct]/8 + [temp.class.spec.match]: specialization
        // matching for the second search (after primary-template
        // substitution of explicit args).
        sfinae_contextt spec_sfinae_guard{*this};

        for(const auto *id_ptr : id_set)
        {
          const symbolt &s = lookup(id_ptr->identifier);
          if(s.type.get(ID_specialization_of).empty())
            continue;

          const cpp_declarationt &spec_decl = to_cpp_declaration(s.type);
          const cpp_template_args_non_tct &partial_args =
            spec_decl.partial_specialization_args();

          if(
            partial_args.arguments().size() !=
            full_args_resolved.arguments().size())
            continue;

          cpp_saved_template_mapt saved_map2(template_map);
          cpp_save_scopet save_scope2(cpp_scopes);

          template_map.build_unassigned(spec_decl.template_type());

          cpp_scopet *spec_scope = id_map_lookup(cpp_scopes, s.name);
          if(spec_scope != nullptr)
            cpp_scopes.go_to(*spec_scope);

          cpp_typecheck_resolvet resolver(*this);

          for(std::size_t i = 0; i < full_args_resolved.arguments().size(); i++)
          {
            if(full_args_resolved.arguments()[i].id() == ID_type)
              resolver.guess_template_args(
                partial_args.arguments()[i].type(),
                full_args_resolved.arguments()[i].type());
            else
              resolver.guess_template_args(
                partial_args.arguments()[i], full_args_resolved.arguments()[i]);
          }

          cpp_template_args_tct guessed =
            template_map.build_template_args(spec_decl.template_type());

          if(guessed.has_unassigned())
            continue;

          cpp_template_args_tct partial_tc;
          bool sfinae_failed = false;
          {
            // [temp.deduct]/8: substituting explicit template args
            // into the partial specialization's parameter list may
            // fail; treat as SFINAE and skip this candidate.
            sfinae_contextt sfinae_guard{*this};
            try
            {
              partial_tc = typecheck_template_args(
                source_location, template_symbol, partial_args);
            }
            catch(...)
            {
              sfinae_failed = true;
            }
          }
          if(sfinae_failed)
            continue;

          if(partial_tc == full_args_resolved)
          {
            // Also check #c_type to distinguish e.g. char from
            // signed char.
            bool c_type_match = true;
            for(std::size_t j = 0; j < partial_tc.arguments().size(); j++)
            {
              const exprt &p = partial_tc.arguments()[j];
              const exprt &f = full_args_resolved.arguments()[j];
              if(
                p.id() == ID_type &&
                p.type().get(ID_C_c_type) != f.type().get(ID_C_c_type))
              {
                c_type_match = false;
                break;
              }
            }
            if(!c_type_match)
              continue;

            // Evaluate concept constraints on template parameters.
            // Skip specializations whose concept is not satisfied.
            {
              const auto &spec_params =
                spec_decl.template_type().template_parameters();
              bool concept_ok = true;
              for(std::size_t pi = 0;
                  pi < spec_params.size() &&
                  pi < full_args_resolved.arguments().size();
                  ++pi)
              {
                const irep_idt &cc =
                  spec_params[pi].get("#C_concept_constraint");
                if(cc.empty())
                  continue;
                const auto concept_ids =
                  cpp_scopes.current_scope().lookup(cc, cpp_scopet::RECURSIVE);
                if(concept_ids.empty())
                  continue;
                const auto *concept_sym =
                  symbol_table.lookup((*concept_ids.begin())->identifier);
                if(!concept_sym || !concept_sym->type.get_bool(ID_is_template))
                  continue;
                const cpp_declarationt &concept_decl =
                  to_cpp_declaration(concept_sym->type);
                if(concept_decl.declarators().empty())
                  continue;
                exprt body = concept_decl.declarators()[0].value();
                if(body.is_nil())
                  continue;
                template_mapt cmap;
                cpp_template_args_tct cargs;
                cargs.arguments().push_back(full_args_resolved.arguments()[pi]);
                cmap.build(concept_decl.template_type(), cargs);
                cmap.apply(body);
                // [temp.constr.constr] + [temp.deduct]/8: concept
                // body evaluation is SFINAE-guarded; failure to
                // substitute or a `false` result means the concept
                // is not satisfied, not an ill-formed program.
                bool old_suppress = suppress_elaborate;
                suppress_elaborate = false;
                try
                {
                  sfinae_contextt sfinae_guard{*this};
                  typecheck_expr(body);
                  simplify(body, *this);
                  if(body.is_false())
                    concept_ok = false;
                }
                catch(...)
                {
                  concept_ok = false;
                }
                suppress_elaborate = old_suppress;
                if(!concept_ok)
                  break;
              }
              if(!concept_ok)
                continue;
            }

            best_match = &s;
            best_spec_args = guessed;
          }
        }

        if(best_match != nullptr)
        {
          return instantiate_template(
            source_location, *best_match, best_spec_args, full_args_resolved);
        }
      }
    }

    // Append template suffix to the declarator name
    {
      cpp_namet &declarator_name = new_decl.declarators()[0].name();
      for(auto &sub : declarator_name.get_sub())
      {
        if(sub.id() == ID_name)
        {
          sub.set(ID_identifier, id2string(sub.get(ID_identifier)) + suffix);
          break;
        }
      }
    }

    // Force elaboration during variable template body processing
    // so that nested type traits (e.g., is_nothrow_destructible<T>::value)
    // can be fully resolved.
    {
      bool old_suppress = suppress_elaborate;
      suppress_elaborate = false;
      convert_non_template_declaration(new_decl);
      suppress_elaborate = old_suppress;
    }

    const symbolt &symb = lookup(new_decl.declarators()[0].get(ID_identifier));

    return symb;
  }

  // For template aliases (typedefs) and function templates where different
  // template arguments may produce the same parameter types (e.g., when a
  // template parameter only affects the return type), append the template
  // suffix to the declarator name so that different instantiations produce
  // different symbols.
  {
    cpp_namet &declarator_name = new_decl.declarators()[0].name();
    for(auto &sub : declarator_name.get_sub())
    {
      if(sub.id() == ID_name)
      {
        sub.set(ID_identifier, id2string(sub.get(ID_identifier)) + suffix);
        break;
      }
    }
  }

  // When a variadic template parameter pack has zero arguments (the args
  // list is shorter than the parameter list), remove pack-expanded
  // parameters from the function declaration and its nested types.
  if(
    full_template_args.arguments().size() <
      template_type.template_parameters().size() &&
    !template_type.template_parameters().empty() &&
    template_type.template_parameters().back().get_bool(ID_ellipsis))
  {
    // Get the pack parameter's short name
    const auto &pack_param = template_type.template_parameters().back();
    const std::string full_id = id2string(pack_param.type().get(ID_identifier));
    auto pos = full_id.rfind("::");
    const std::string pack_name =
      pos != std::string::npos ? full_id.substr(pos + 2) : full_id;

    // Helper: check if a parameter references the pack
    auto refs_pack = [&pack_name](const irept &p) -> bool
    {
      if(p.id() == ID_ellipsis)
        return true;
      if(p.id() == ID_cpp_declaration)
      {
        const auto &d = to_cpp_declaration(p);
        if(
          !d.declarators().empty() &&
          d.declarators().front().type().get_bool(ID_ellipsis))
          return true;
        if(d.type().id() == ID_cpp_name)
        {
          for(const auto &sub : d.type().get_sub())
          {
            if(
              sub.id() == ID_name &&
              id2string(sub.get(ID_identifier)) == pack_name)
              return true;
          }
        }
      }
      return false;
    };

    // Strip from the function's own parameters
    auto &func_decl = new_decl.declarators()[0];
    irept &func_params = func_decl.type().add(ID_parameters);
    irept::subt &fp_sub = func_params.get_sub();

    // Get the pack variable name before removing (e.g. "base" from
    // "Base... base")
    irep_idt pack_var_name;
    for(const auto &fp : fp_sub)
    {
      if(fp.id() == ID_cpp_declaration)
      {
        const auto &d = to_cpp_declaration(fp);
        if(
          !d.declarators().empty() &&
          d.declarators().front().type().get_bool(ID_ellipsis))
        {
          const auto &dname = d.declarators().front().name();
          for(const auto &sub : dname.get_sub())
          {
            if(sub.id() == ID_name)
            {
              pack_var_name = sub.get(ID_identifier);
              break;
            }
          }
          break;
        }
      }
    }

    fp_sub.erase(
      std::remove_if(fp_sub.begin(), fp_sub.end(), refs_pack), fp_sub.end());

    // Strip from nested function pointer parameter types
    for(auto &fp : fp_sub)
    {
      if(fp.id() == ID_cpp_declaration)
      {
        auto &inner_decl = to_cpp_declaration(fp);
        if(!inner_decl.declarators().empty())
        {
          irept &dtype = inner_decl.declarators().front().type();
          if(
            dtype.id() == ID_frontend_pointer && !dtype.get_sub().empty() &&
            dtype.get_sub().front().id() == ID_function_type)
          {
            irept::subt &inner_params =
              dtype.get_sub().front().add(ID_parameters).get_sub();
            inner_params.erase(
              std::remove_if(
                inner_params.begin(), inner_params.end(), refs_pack),
              inner_params.end());
          }
        }
      }
    }
    // Strip pack variable references from function call arguments in body
    if(!pack_var_name.empty() && func_decl.value().is_not_nil())
    {
      // Recursively remove pack variable from function call arguments
      std::function<void(irept &)> strip_pack_var;
      strip_pack_var = [&pack_var_name, &strip_pack_var](irept &node)
      {
        // If this is a function_call side_effect, strip pack var from args
        if(
          node.id() == ID_side_effect &&
          node.get(ID_statement) == ID_function_call)
        {
          // Arguments are stored as a positional sub-node with id=arguments
          for(auto &sub : node.get_sub())
          {
            if(sub.id() == ID_arguments)
            {
              irept::subt &arg_sub = sub.get_sub();
              arg_sub.erase(
                std::remove_if(
                  arg_sub.begin(),
                  arg_sub.end(),
                  [&pack_var_name](const irept &a)
                  {
                    if(a.id() == ID_cpp_name)
                    {
                      for(const auto &s : a.get_sub())
                      {
                        if(
                          s.id() == ID_name &&
                          s.get(ID_identifier) == pack_var_name)
                          return true;
                      }
                    }
                    return false;
                  }),
                arg_sub.end());
              break;
            }
          }
        }
        // Recurse into sub-nodes
        for(auto &sub : node.get_sub())
          strip_pack_var(sub);
        // Also recurse into named sub-nodes
        for(auto &named : node.get_named_sub())
          strip_pack_var(named.second);
      };
      strip_pack_var(func_decl.value());
    }
  }

  // When a variadic template parameter pack has N>0 arguments, expand
  // the pack parameter into N individual function parameters and expand
  // pack references in the function body.
  if(
    full_template_args.arguments().size() >
      template_type.template_parameters().size() &&
    !template_type.template_parameters().empty() &&
    template_type.template_parameters().back().get_bool(ID_ellipsis))
  {
    const std::size_t non_pack = template_type.template_parameters().size() - 1;
    const std::size_t pack_sz =
      full_template_args.arguments().size() - non_pack;

    auto &func_decl = new_decl.declarators()[0];
    irept &func_params = func_decl.type().add(ID_parameters);
    irept::subt &fp_sub = func_params.get_sub();

    // Find the pack parameter (last param with ellipsis on declarator)
    int pack_idx = -1;
    irep_idt pack_var_name;
    for(int i = static_cast<int>(fp_sub.size()) - 1; i >= 0; --i)
    {
      if(fp_sub[i].id() == ID_cpp_declaration)
      {
        const auto &d = to_cpp_declaration(fp_sub[i]);
        if(
          !d.declarators().empty() &&
          d.declarators().front().type().get_bool(ID_ellipsis))
        {
          pack_idx = i;
          const auto &dname = d.declarators().front().name();
          for(const auto &sub : dname.get_sub())
          {
            if(sub.id() == ID_name)
            {
              pack_var_name = sub.get(ID_identifier);
              break;
            }
          }
          break;
        }
      }
    }

    if(pack_idx >= 0 && !pack_var_name.empty())
    {
      // Build expanded parameters
      irept pack_param_template = fp_sub[pack_idx];
      // Remove ellipsis from template
      {
        auto &d = static_cast<cpp_declarationt &>(pack_param_template);
        d.declarators().front().type().remove(ID_ellipsis);
      }

      std::vector<irep_idt> expanded_names;
      std::vector<irept> expanded_params;
      for(std::size_t k = 0; k < pack_sz; ++k)
      {
        irept param_copy = pack_param_template;
        const std::string new_name =
          id2string(pack_var_name) + "$" + std::to_string(k);
        expanded_names.push_back(irep_idt(new_name));

        // Set the parameter type from the k-th pack argument
        const exprt &pack_arg = full_template_args.arguments()[non_pack + k];
        if(pack_arg.id() == ID_type)
        {
          auto &d = static_cast<cpp_declarationt &>(param_copy);
          d.type() = pack_arg.type();
        }

        // Rename the parameter
        auto &d = static_cast<cpp_declarationt &>(param_copy);
        if(!d.declarators().empty())
        {
          auto &dname = d.declarators().front().name();
          for(auto &sub : dname.get_sub())
          {
            if(sub.id() == ID_name)
            {
              sub.set(ID_identifier, new_name);
              break;
            }
          }
        }
        expanded_params.push_back(param_copy);
      }

      // Replace the pack parameter with expanded parameters
      fp_sub.erase(fp_sub.begin() + pack_idx);
      fp_sub.insert(
        fp_sub.begin() + pack_idx,
        expanded_params.begin(),
        expanded_params.end());

      // Expand pack references in the function body
      if(func_decl.value().is_not_nil())
      {
        // Helper: check if an irept is a cpp_name referencing pack_var
        auto is_pack_name = [&pack_var_name](const irept &n) -> bool
        {
          if(n.id() != ID_cpp_name)
            return false;
          for(const auto &s : n.get_sub())
          {
            if(s.id() == ID_name && s.get(ID_identifier) == pack_var_name)
              return true;
          }
          return false;
        };

        // Helper: make a cpp_name for an expanded parameter
        auto make_name = [](const irept &orig, const irep_idt &name)
        {
          irept copy = orig;
          for(auto &s : copy.get_sub())
          {
            if(s.id() == ID_name)
            {
              s.set(ID_identifier, name);
              break;
            }
          }
          return copy;
        };

        // Helper: check if an irept contains a pack_name anywhere
        std::function<bool(const irept &)> contains_pack_name;
        contains_pack_name = [&is_pack_name,
                              &contains_pack_name](const irept &n) -> bool
        {
          if(is_pack_name(n))
            return true;
          for(const auto &s : n.get_sub())
            if(contains_pack_name(s))
              return true;
          for(const auto &ns : n.get_named_sub())
            if(contains_pack_name(ns.second))
              return true;
          return false;
        };

        // Helper: substitute pack_name within an expression
        std::function<irept(const irept &, const irep_idt &)> substitute_pack;
        substitute_pack = [&is_pack_name, &make_name, &substitute_pack](
                            const irept &n, const irep_idt &name) -> irept
        {
          if(is_pack_name(n))
            return make_name(n, name);
          irept result = n;
          for(auto &s : result.get_sub())
            s = substitute_pack(s, name);
          return result;
        };

        std::function<void(irept &)> expand_pack;
        expand_pack = [&expanded_names,
                       &expand_pack,
                       &is_pack_name,
                       &contains_pack_name,
                       &substitute_pack,
                       &make_name](irept &node)
        {
          // Expand fold expressions
          if(
            (node.id() == irep_idt("cpp_right_fold") ||
             node.id() == irep_idt("cpp_left_fold")) &&
            !node.get_sub().empty() &&
            contains_pack_name(node.get_sub().front()))
          {
            const irep_idt fold_op = node.get(irep_idt("fold_op"));
            const irept &pack_expr = node.get_sub().front();
            bool is_left = (node.id() == irep_idt("cpp_left_fold"));

            if(expanded_names.size() == 1)
            {
              node = substitute_pack(pack_expr, expanded_names[0]);
              return;
            }

            // Build binary expression tree
            if(is_left)
            {
              // Left fold: ((a op b) op c)
              irept result = substitute_pack(pack_expr, expanded_names[0]);
              for(std::size_t i = 1; i < expanded_names.size(); ++i)
              {
                irept bin(fold_op);
                bin.get_sub().push_back(result);
                bin.get_sub().push_back(
                  substitute_pack(pack_expr, expanded_names[i]));
                result = bin;
              }
              node = result;
            }
            else
            {
              // Right fold: (a op (b op c))
              irept result = substitute_pack(
                pack_expr, expanded_names[expanded_names.size() - 1]);
              for(int i = static_cast<int>(expanded_names.size()) - 2; i >= 0;
                  --i)
              {
                irept bin(fold_op);
                bin.get_sub().push_back(
                  substitute_pack(pack_expr, expanded_names[i]));
                bin.get_sub().push_back(result);
                result = bin;
              }
              node = result;
            }
            return;
          }

          // Expand binary fold expressions: (init op ... op pack)
          if(
            node.id() == irep_idt("cpp_binary_fold") &&
            node.get_sub().size() >= 2 && contains_pack_name(node.get_sub()[1]))
          {
            const irep_idt fold_op = node.get(irep_idt("fold_op"));
            const irept &init_expr = node.get_sub()[0];
            const irept &pack_expr = node.get_sub()[1];

            // Binary left fold: ((init op pack[0]) op pack[1]) op ...
            irept result = init_expr;
            for(std::size_t i = 0; i < expanded_names.size(); ++i)
            {
              irept bin(fold_op);
              bin.get_sub().push_back(result);
              bin.get_sub().push_back(
                substitute_pack(pack_expr, expanded_names[i]));
              result = bin;
            }
            node = result;
            return;
          }

          // Look for function call arguments containing pack_var...
          if(
            node.id() == ID_side_effect &&
            node.get(ID_statement) == ID_function_call)
          {
            for(auto &sub : node.get_sub())
            {
              if(sub.id() != ID_arguments)
                continue;
              irept::subt &arg_sub = sub.get_sub();
              irept::subt new_args;
              for(auto &a : arg_sub)
              {
                if(is_pack_name(a))
                {
                  // Expand into individual arguments
                  for(const auto &ename : expanded_names)
                    new_args.push_back(make_name(a, ename));
                }
                else
                {
                  new_args.push_back(a);
                }
              }
              arg_sub = new_args;
              break;
            }
          }

          // Expand lambda pack init-captures: [...x = args]
          if(node.id() == irep_idt("lambda"))
          {
            irept &cap_list = node.add("lambda_capture");
            irept::subt new_caps;
            irep_idt cap_pack_name;
            std::vector<irep_idt> cap_expanded_names;
            for(auto &cap : cap_list.get_sub())
            {
              if(
                cap.get_bool("is_pack") && contains_pack_name(cap.find("init")))
              {
                cap_pack_name = cap.get(ID_identifier);
                for(std::size_t i = 0; i < expanded_names.size(); ++i)
                {
                  irept new_cap = cap;
                  new_cap.remove("is_pack");
                  irep_idt ename =
                    id2string(cap_pack_name) + "_" + std::to_string(i);
                  new_cap.set(ID_identifier, ename);
                  new_cap.add("init") =
                    substitute_pack(cap.find("init"), expanded_names[i]);
                  new_caps.push_back(new_cap);
                  cap_expanded_names.push_back(ename);
                }
              }
              else
              {
                new_caps.push_back(cap);
              }
            }
            cap_list.get_sub() = new_caps;

            // Expand fold expressions in the lambda body that reference
            // the captured pack name.
            if(!cap_pack_name.empty())
            {
              auto is_cap_name = [&cap_pack_name](const irept &n) -> bool
              {
                if(n.id() != ID_cpp_name)
                  return false;
                for(const auto &s : n.get_sub())
                  if(s.id() == ID_name && s.get(ID_identifier) == cap_pack_name)
                    return true;
                return false;
              };
              auto make_cap_name = [](const irept &orig, const irep_idt &name)
              {
                irept copy = orig;
                for(auto &s : copy.get_sub())
                  if(s.id() == ID_name)
                  {
                    s.set(ID_identifier, name);
                    break;
                  }
                return copy;
              };
              auto sub_cap =
                [&is_cap_name, &make_cap_name](
                  const irept &n, const irep_idt &name, auto &self) -> irept
              {
                if(is_cap_name(n))
                  return make_cap_name(n, name);
                irept result = n;
                for(auto &s : result.get_sub())
                  s = self(s, name, self);
                return result;
              };
              auto contains_cap =
                [&is_cap_name](const irept &n, auto &self) -> bool
              {
                if(is_cap_name(n))
                  return true;
                for(const auto &s : n.get_sub())
                  if(self(s, self))
                    return true;
                for(const auto &ns : n.get_named_sub())
                  if(self(ns.second, self))
                    return true;
                return false;
              };

              std::function<void(irept &)> expand_cap_fold;
              expand_cap_fold = [&](irept &n)
              {
                if(
                  (n.id() == irep_idt("cpp_right_fold") ||
                   n.id() == irep_idt("cpp_left_fold")) &&
                  !n.get_sub().empty() &&
                  contains_cap(n.get_sub().front(), contains_cap))
                {
                  const irep_idt fold_op = n.get(irep_idt("fold_op"));
                  const irept &pe = n.get_sub().front();
                  bool is_left = (n.id() == irep_idt("cpp_left_fold"));
                  if(cap_expanded_names.size() == 1)
                  {
                    n = sub_cap(pe, cap_expanded_names[0], sub_cap);
                    return;
                  }
                  if(is_left)
                  {
                    irept r = sub_cap(pe, cap_expanded_names[0], sub_cap);
                    for(std::size_t i = 1; i < cap_expanded_names.size(); ++i)
                    {
                      irept bin(fold_op);
                      bin.get_sub().push_back(r);
                      bin.get_sub().push_back(
                        sub_cap(pe, cap_expanded_names[i], sub_cap));
                      r = bin;
                    }
                    n = r;
                  }
                  else
                  {
                    irept r = sub_cap(
                      pe,
                      cap_expanded_names[cap_expanded_names.size() - 1],
                      sub_cap);
                    for(int i = static_cast<int>(cap_expanded_names.size()) - 2;
                        i >= 0;
                        --i)
                    {
                      irept bin(fold_op);
                      bin.get_sub().push_back(
                        sub_cap(pe, cap_expanded_names[i], sub_cap));
                      bin.get_sub().push_back(r);
                      r = bin;
                    }
                    n = r;
                  }
                  return;
                }
                // Binary fold: (init op ... op pack)
                if(
                  n.id() == irep_idt("cpp_binary_fold") &&
                  n.get_sub().size() >= 2 &&
                  contains_cap(n.get_sub()[1], contains_cap))
                {
                  const irep_idt fold_op = n.get(irep_idt("fold_op"));
                  const irept &init_e = n.get_sub()[0];
                  const irept &pe = n.get_sub()[1];
                  irept r = init_e;
                  for(std::size_t i = 0; i < cap_expanded_names.size(); ++i)
                  {
                    irept bin(fold_op);
                    bin.get_sub().push_back(r);
                    bin.get_sub().push_back(
                      sub_cap(pe, cap_expanded_names[i], sub_cap));
                    r = bin;
                  }
                  n = r;
                  return;
                }
                for(auto &s : n.get_sub())
                  expand_cap_fold(s);
                for(auto &ns : n.get_named_sub())
                  expand_cap_fold(ns.second);
              };
              // The lambda body is a named sub-tree
              for(auto &ns : node.get_named_sub())
                expand_cap_fold(ns.second);
              for(auto &s : node.get_sub())
                expand_cap_fold(s);
            }
          }

          for(auto &sub : node.get_sub())
            expand_pack(sub);
          for(auto &named : node.get_named_sub())
            expand_pack(named.second);
        };
        expand_pack(func_decl.value());
      }
    }
  }

  // Per [temp.variadic]/7: remove empty pack expansions
  if(!template_map.pack_size_map.empty() && !new_decl.declarators().empty())
  {
    // Per [basic.scope.temp] and [temp.variadic]/5: a pack parameter's
    // short name in this template refers to THIS template's pack
    // parameter, not a pack with the same short name declared by
    // some other template that happens to be in the pack_size_map.
    // Restrict to packs declared by the template being instantiated
    // so that `_Types` from one template doesn't cause parameters of
    // another template to be stripped.
    std::set<irep_idt> local_pack_ids;
    for(const auto &tp : template_type.template_parameters())
    {
      if(tp.get_bool(ID_ellipsis))
      {
        irep_idt pid = tp.type().get(ID_identifier);
        if(!pid.empty())
          local_pack_ids.insert(pid);
      }
    }
    std::set<std::string> ep;
    for(const auto &ps : template_map.pack_size_map)
      if(ps.second == 0 && local_pack_ids.count(ps.first))
      {
        const std::string f = id2string(ps.first);
        auto p = f.rfind("::");
        ep.insert(p != std::string::npos ? f.substr(p + 2) : f);
      }
    if(!ep.empty())
    {
      std::function<bool(const irept &)> has_ep = [&](const irept &n) -> bool
      {
        if(n.id() == ID_template_parameter_symbol_type)
        {
          const std::string f = id2string(n.get(ID_identifier));
          auto p = f.rfind("::");
          if(ep.count(p != std::string::npos ? f.substr(p + 2) : f))
            return true;
        }
        if(n.id() == ID_name && ep.count(id2string(n.get(ID_identifier))))
          return true;
        for(const auto &s : n.get_sub())
          if(has_ep(s))
            return true;
        for(const auto &ns : n.get_named_sub())
          if(has_ep(ns.second))
            return true;
        return false;
      };
      auto &dt = new_decl.declarators()[0].type();
      if(dt.id() == ID_function_type)
      {
        irept &params = dt.add(ID_parameters);
        params.get_sub().erase(
          std::remove_if(
            params.get_sub().begin(),
            params.get_sub().end(),
            [&](const irept &p)
            {
              if(p.id() != ID_cpp_declaration)
                return false;
              for(const auto &d : p.get_sub())
              {
                if(
                  d.id() == ID_cpp_declarator &&
                  (d.find(ID_type).get_bool(ID_ellipsis) ||
                   d.get_bool(ID_ellipsis)))
                  return true;
                // Also check for empty pack parameter type
                if(d.id() == ID_cpp_declarator)
                {
                  const auto &dtype = d.find(ID_type);
                  if(has_ep(dtype))
                    return true;
                }
              }
              // Check declaration type
              if(has_ep(p.find(ID_type)))
                return true;
              return false;
            }),
          params.get_sub().end());
      }
      irept &mi = new_decl.declarators()[0].add(ID_member_initializers);
      for(auto &init : mi.get_sub())
      {
        auto &subs = init.get_sub();
        subs.erase(
          std::remove_if(
            subs.begin(),
            subs.end(),
            [&](const irept &s) { return has_ep(s); }),
          subs.end());
      }
    }
  }

  convert_non_template_declaration(new_decl);

  const symbolt &symb=
    lookup(new_decl.declarators()[0].get(ID_identifier));

  return symb;
}
