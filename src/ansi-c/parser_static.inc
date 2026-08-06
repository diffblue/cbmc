#include <util/c_types.h>
#include <util/std_code.h>
#include <util/string2int.h>

#include "merged_type.h"

#define YYSTYPE unsigned
#define YYSTYPE_IS_TRIVIAL 1

#define mto(x, y) parser_stack(x).add_to_operands(std::move(parser_stack(y)))
#define mts(x, y) (to_type_with_subtypes(stack_type(x)).move_to_subtypes(stack_type(y)))
#define binary(x, y, l, id, z) { init(x, id); \
  parser_stack(x).add_source_location()=parser_stack(l).source_location(); \
  parser_stack(x).add_to_operands(std::move(parser_stack(y)), std::move(parser_stack(z))); }

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void init(YYSTYPE &expr)
{
  newstack(expr);
}

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static void init(YYSTYPE &expr, const irep_idt &id)
{
  newstack(expr);
  parser_stack(expr).id(id);
}

/*******************************************************************\

Function: set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static void set(YYSTYPE expr, const irep_idt &id)
{
  parser_stack(expr).id(id);
}

/*******************************************************************\

Function: statement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void statement(YYSTYPE &expr, const irep_idt &id)
{
  set(expr, ID_code);
  parser_stack(expr).set(ID_statement, id);
}

/*******************************************************************\

Function: merge_types

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void merge_types(irept &dest, irept &src)
{
  #if 0
  std::cout << "D: " << dest.pretty() << '\n';
  std::cout << "S: " << src.pretty() << '\n';
  #endif

  if(src.is_nil())
    return;

  if(dest.is_nil())
  {
    dest=src;
    return;
  }

  if(dest.id()!=ID_merged_type)
  {
    source_locationt location=static_cast<const exprt &>(dest).source_location();
    merged_typet new_type;
    new_type.move_to_subtypes((typet &)(dest));
    dest.swap(new_type);
    static_cast<exprt &>(dest).add_source_location()=location;
  }

  to_type_with_subtypes(static_cast<typet &>(dest)).move_to_subtypes(static_cast<typet &>(src));
}

/*******************************************************************\

Function: merge_types

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
static void merge_types(const YYSTYPE dest, const YYSTYPE src)
{
  merge_types(parser_stack(dest), parser_stack(src));
}
#endif

/*******************************************************************\

Function: merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static YYSTYPE merge(const YYSTYPE src1, const YYSTYPE src2)
{
  merge_types(parser_stack(src1), parser_stack(src2));
  return src1;
}

/*******************************************************************\

Function: make_subtype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void make_subtype(typet &dest, typet &src)
{
  // inserts "src" into "dest"
  // e.g., src is a pointer or array,
  // dest is a symbol or type

  // find spot in 'dest' where to insert 'src'

  #if 0
  std::cout << "D: " << dest.pretty() << '\n';
  std::cout << "S: " << src.pretty() << '\n';
  #endif

  PRECONDITION(src.id()==ID_array ||
         src.id()==ID_frontend_pointer ||
         src.id()==ID_code ||
         src.id()==ID_merged_type ||
         src.id()==ID_abstract ||
         src.id()==ID_c_bit_field);

  typet *p=&dest;

  while(true)
  {
    // see if we need to walk down
    typet *sub=p;

    if(p->id()==ID_merged_type)
    {
      // do last one
      auto &merged_type = to_merged_type(*p);
      sub = &merged_type.last_type();
    }

    if(sub->id()==ID_frontend_pointer ||
       sub->id()==ID_array ||
       sub->id()==ID_code)
    {
      // walk down
      p=&sub->add_subtype();
    }
    else
    {
      if(p->id()==ID_abstract)
      {
        p->swap(src);
        break;
      }
      else if(p->is_nil())
        UNREACHABLE;
      else if(p->id().empty())
        UNREACHABLE;
      else
      {
        // *p is now type or symbol

        // save symbol
        typet symbol=*p;
        p->swap(src);

        // find spot where to put symbol
        while(true)
        {
          if(p->id()==ID_abstract)
          {
            p->swap(symbol);
            break;
          }
          else if(p->id()==ID_merged_type)
          {
            auto &merged_type = to_merged_type(*p);
            p=&merged_type.last_type();
          }
          else if(p->id().empty())
            UNREACHABLE;
          else if(p->is_nil())
            UNREACHABLE;
          else
            p=&p->add_subtype();
        }
        break;
      }
    }
  }
}

/*******************************************************************\

Function: make_subtype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void make_subtype(YYSTYPE dest, YYSTYPE src)
{
  make_subtype(stack_type(dest), stack_type(src));
}

/*******************************************************************\

Function: make_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void make_pointer(const YYSTYPE dest)
{
  // The below deliberately avoids pointer_type().
  // The width is set during conversion.
  stack_type(dest).id(ID_frontend_pointer);
  stack_type(dest).add_subtype()=typet(ID_abstract);
}

/*******************************************************************\

Function: do_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void do_pointer(const YYSTYPE ptr, const YYSTYPE dest)
{
  make_pointer(ptr);
  make_subtype(dest, ptr);
}

/*******************************************************************\

Function: create_function_scope

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void create_function_scope(const YYSTYPE d)
{
  ansi_c_declarationt &declaration=to_ansi_c_declaration(parser_stack(d));
  ansi_c_declaratort &declarator=declaration.declarator();

  irep_idt function_name=declarator.get_base_name();

  // record which function we are in
  PARSER.set_function(function_name);

  std::string prefix=PARSER.current_scope().prefix+
                     id2string(function_name)+"::";
  PARSER.new_scope(prefix);

  // We look at the last type in case of a merged declarator type.
  typet *declarator_type = &declarator.type();
  if(declarator_type->id()==ID_merged_type)
  {
    // we want the last one
    auto &merged_type = to_merged_type(*declarator_type);
    declarator_type = &merged_type.last_type();
  }

  // The grammar doesn't actually enforce that a function type
  // is used to define a function body. We will complain in the
  // type checker about it.
  if(declarator_type->id()==ID_code)
  {
    code_typet &code_type=to_code_type(*declarator_type);

    code_typet::parameterst &parameters=code_type.parameters();

    // Add the parameter declarations to the scope.
    for(auto &param : parameters)
    {
      if(param.id()==ID_declaration)
      {
        ansi_c_declarationt &param_decl=to_ansi_c_declaration(param);

        // we record the function name in the location
        param_decl.add_source_location().set_function(function_name);

        if(!param_decl.declarators().empty())
        {
          // add to scope
          irep_idt base_name=param_decl.declarator().get_base_name();
          ansi_c_identifiert &identifier=
            PARSER.current_scope().name_map[base_name];
          identifier.id_class=ansi_c_id_classt::ANSI_C_SYMBOL;
          identifier.base_name=base_name;
          identifier.prefixed_name=param_decl.declarator().get_name();
        }
      }
    }
  }
}

/*******************************************************************\

Function: adjust_KnR_parameters

  Inputs:

 Outputs:

 Purpose: this patches the KnR parameter types into the
          function type

\*******************************************************************/

static void adjust_KnR_parameters(
  irept &parameters,
  exprt &declarations)
{
  // the below is probably better done in the type checker

  Forall_operands(d_it, declarations)
  {
    DATA_INVARIANT(d_it->id()==ID_declaration, "expected declaration");
    ansi_c_declarationt &declaration=
      to_ansi_c_declaration(static_cast<exprt &>(*d_it));

    // Go over declarators
    ansi_c_declarationt::declaratorst &declarators=
      declaration.declarators();

    for(const auto &decl : declarators)
    {
      irep_idt base_name=decl.get_base_name();

      // we just do a linear search over the parameters
      // this could be improved with a hash map
      for(auto &parameter : parameters.get_sub())
      {
        ansi_c_declarationt &p_decl=
          to_ansi_c_declaration(static_cast<exprt &>(parameter));

        if(p_decl.declarator().get_base_name()==base_name)
        {
          // match
          // This copies the declaration type, which can be a
          // problem if there are compound bodies in there.
          p_decl.type()=declaration.type();
          p_decl.declarator().type()=decl.type();
          break;
        }
      }
    }
  }
}

/*******************************************************************\

Function: nested_function_setup

  Inputs: d - the YYSTYPE of a `declaration` node already initialised
              with the merged type and declarator for a nested
              function definition.

 Outputs: A small POD aggregating the bookkeeping needed to undo the
          parser-side effects of `add_declarator` for a nested
          function. Pass it back to `nested_function_teardown` after
          parsing the function body.

 Purpose: Prepare the parser state for a GCC nested function
          definition. `add_declarator` always treats functions as
          living in the root scope: it sets the declarator's name to
          the bare base name and writes an entry into
          `root_scope().name_map[base]`. For a nested function we
          want the symbol to live in the *enclosing* function's scope
          instead, and we must not damage any pre-existing global
          mapping for the same base name.

          This helper rewrites the declarator's name to the
          enclosing-scope-prefixed form, fixes up the current scope's
          name_map entry to match, and restores any prior root-scope
          entry (or removes the one freshly written by `add_declarator`
          if there was no prior entry). It also records the parser's
          current function name so that `nested_function_teardown`
          can restore it after the nested body has been parsed,
          rather than clearing it (which would lose the outer
          function context for subsequent statements in the
          enclosing body).

\*******************************************************************/

static ansi_c_parsert::nested_function_contextt
nested_function_setup(const YYSTYPE d)
{
  ansi_c_declaratort &declarator =
    to_ansi_c_declaration(parser_stack(d)).declarator();
  const irep_idt base = declarator.get_base_name();

  ansi_c_parsert::nested_function_contextt ctx;
  ctx.base_name = base;
  // Capture the outer function name *before* create_function_scope
  // overwrites it with the nested function's name. We restore this in
  // nested_function_teardown so that statements parsed after the
  // nested function definition keep the outer function as their
  // source_location.function (relevant for `__func__` and any other
  // consumer of that field).
  ctx.outer_function_name = PARSER.source_location().get_function();

  // add_declarator forced this function into the root scope. Rewrite
  // the declarator name to use the enclosing scope's prefix, and fix
  // up the current scope's name_map entry to match.
  const irep_idt local_name = PARSER.current_scope().prefix + id2string(base);
  declarator.set_name(local_name);
  PARSER.current_scope().name_map[base].prefixed_name = local_name;

  // Snapshot any pre-existing root-scope entry for this base name
  // before we drop the entry that add_declarator just installed.
  // After the nested function has been parsed we restore the prior
  // entry (if any), so a global symbol with the same base name keeps
  // its parser-side mapping. If there was no prior entry, we just
  // erase the freshly-written one.
  auto root_it = PARSER.root_scope().name_map.find(base);
  if(root_it != PARSER.root_scope().name_map.end())
  {
    ctx.had_prior_root_entry = true;
    ctx.prior_root_entry = root_it->second;
  }
  else
  {
    ctx.had_prior_root_entry = false;
  }

  return ctx;
}

/*******************************************************************\

Function: nested_function_teardown

  Inputs: ctx - the bookkeeping returned by nested_function_setup.

 Outputs:

 Purpose: Undo the root-scope side effects of `add_declarator` for a
          nested function and restore the enclosing function's
          source-location context. Call after `pop_scope()` for the
          nested function's body.

\*******************************************************************/

static void
nested_function_teardown(const ansi_c_parsert::nested_function_contextt &ctx)
{
  // Restore (or erase) the root-scope name_map entry. We always
  // overwrite, because add_declarator unconditionally wrote an entry
  // for `base` into root_scope.
  if(ctx.had_prior_root_entry)
    PARSER.root_scope().name_map[ctx.base_name] = ctx.prior_root_entry;
  else
    PARSER.root_scope().name_map.erase(ctx.base_name);

  // Restore the outer function context (the parser-wide source
  // location's function field) rather than clearing it: parsing
  // continues inside the enclosing function body, and code there
  // should still be tagged with the enclosing function name.
  if(ctx.outer_function_name.empty())
    PARSER.clear_function();
  else
    PARSER.set_function(ctx.outer_function_name);
}

/*******************************************************************\

Function: nested_function_definition_head

  Inputs: result - YYSTYPE for the resulting declaration;
          type - YYSTYPE holding the (return) type specifier;
          declarator - YYSTYPE holding the function declarator (with any
            post-declarator attributes already merged in).

 Outputs:

 Purpose: Shared mid-rule action for the alternatives of
          gcc_nested_function_definition. Builds the ansi_c_declaration
          for the nested function head, relocates it from the root scope
          into the enclosing local scope (remembering the outer function
          context via nested_function_setup), and opens the nested
          function's scope. Mirrors function_head, plus the nested-scope
          relocation.

\*******************************************************************/

static void nested_function_definition_head(
  YYSTYPE &result,
  YYSTYPE type,
  YYSTYPE declarator)
{
  init(result, ID_declaration);
  parser_stack(result).type().swap(parser_stack(type));
  PARSER.add_declarator(parser_stack(result), parser_stack(declarator));
  PARSER.nested_function_context_stack.push_back(nested_function_setup(result));
  create_function_scope(result);
}

/*******************************************************************\

Function: nested_function_definition_body

  Inputs: result - YYSTYPE for the resulting declaration statement;
          declaration - YYSTYPE holding the ansi_c_declaration produced
            by nested_function_definition_head;
          body - YYSTYPE holding the parsed function body.

 Outputs:

 Purpose: Shared post-body action for the alternatives of
          gcc_nested_function_definition. Attaches the body as the
          declaration's initialiser, closes the nested function's scope,
          restores the enclosing function context, and wraps the result
          as a declaration statement so it fits inside a block.

\*******************************************************************/

static void nested_function_definition_body(
  YYSTYPE &result,
  YYSTYPE declaration,
  YYSTYPE body)
{
  ansi_c_declarationt &ansi_c_declaration =
    to_ansi_c_declaration(parser_stack(declaration));
  DATA_INVARIANT(
    ansi_c_declaration.declarators().size() == 1, "exactly one declarator");
  ansi_c_declaration.add_initializer(parser_stack(body));
  PARSER.pop_scope();
  nested_function_teardown(PARSER.nested_function_context_stack.back());
  PARSER.nested_function_context_stack.pop_back();

  // Wrap as a declaration statement so it fits in a block.
  init(result);
  statement(result, ID_decl);
  mto(result, declaration);
}
