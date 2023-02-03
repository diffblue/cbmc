/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ansi_c_entry_point.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/symbol_table_base.h>

#include <goto-programs/goto_functions.h>

#include <linking/static_lifetime_init.h>

#include "c_nondet_symbol_factory.h"
#include "expr2c.h"

exprt::operandst build_function_environment(
  const code_typet::parameterst &parameters,
  code_blockt &init_code,
  symbol_table_baset &symbol_table,
  const c_object_factory_parameterst &object_factory_parameters)
{
  exprt::operandst main_arguments;
  main_arguments.resize(parameters.size());

  for(std::size_t param_number=0;
      param_number<parameters.size();
      param_number++)
  {
    const code_typet::parametert &p=parameters[param_number];
    const irep_idt base_name=p.get_base_name().empty()?
      ("argument#"+std::to_string(param_number)):p.get_base_name();

    main_arguments[param_number] = c_nondet_symbol_factory(
      init_code,
      symbol_table,
      base_name,
      p.type(),
      p.source_location(),
      object_factory_parameters,
      lifetimet::AUTOMATIC_LOCAL);
  }

  return main_arguments;
}

void record_function_outputs(
  const symbolt &function,
  code_blockt &init_code,
  symbol_table_baset &symbol_table)
{
  bool has_return_value =
    to_code_type(function.type).return_type() != void_type();

  if(has_return_value)
  {
    const symbolt &return_symbol = symbol_table.lookup_ref("return'");

    // record return value
    init_code.add(code_outputt{
      return_symbol.base_name, return_symbol.symbol_expr(), function.location});
  }

  #if 0
  std::size_t i=0;

  for(const auto &p : parameters)
  {
    if(p.get_identifier().empty())
      continue;

    irep_idt identifier=p.get_identifier();

    const symbolt &symbol=symbol_table.lookup(identifier);

    if(symbol.type.id()==ID_pointer)
    {
      codet output(ID_output);
      output.operands().resize(2);

      output.op0()=
        address_of_exprt(
          index_exprt(
            string_constantt(symbol.base_name),
            from_integer(0, index_type())));
      output.op1()=symbol.symbol_expr();
      output.add_source_location()=p.source_location();

      init_code.add(std::move(output));
    }

    i++;
  }
  #endif
}

bool ansi_c_entry_point(
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  const c_object_factory_parameterst &object_factory_parameters)
{
  // check if entry point is already there
  if(symbol_table.symbols.find(goto_functionst::entry_point())!=
     symbol_table.symbols.end())
    return false; // silently ignore

  irep_idt main_symbol;

  // find main symbol, if any is given
  if(config.main.has_value())
  {
    auto matches = symbol_table.match_name_or_base_name(*config.main);

    for(auto it = matches.begin(); it != matches.end();) // no ++it
    {
      if((*it)->second.type.id() != ID_code || (*it)->second.is_property)
        it = matches.erase(it);
      else
        ++it;
    }

    if(matches.empty())
    {
      messaget message(message_handler);
      message.error() << "main symbol '" << config.main.value() << "' not found"
                      << messaget::eom;
      return true; // give up
    }

    if(matches.size()>=2)
    {
      messaget message(message_handler);
      message.error() << "main symbol '" << config.main.value()
                      << "' is ambiguous" << messaget::eom;
      return true;
    }

    main_symbol = matches.front()->first;
  }
  else
    main_symbol=ID_main;

  // look it up
  symbol_table_baset::symbolst::const_iterator s_it =
    symbol_table.symbols.find(main_symbol);

  if(s_it==symbol_table.symbols.end())
    return false; // give up silently

  const symbolt &symbol=s_it->second;

  // check if it has a body
  if(symbol.value.is_nil())
  {
    messaget message(message_handler);
    message.error() << "main symbol '" << id2string(main_symbol)
                    << "' has no body" << messaget::eom;
    return false; // give up
  }

  static_lifetime_init(symbol_table, symbol.location);

  return generate_ansi_c_start_function(
    symbol, symbol_table, message_handler, object_factory_parameters);
}

/// Generate a _start function for a specific function
/// \param symbol: The symbol for the function that should be
///   used as the entry point
/// \param symbol_table: The symbol table for the program. The new _start
///   function symbol will be added to this table
/// \param message_handler: The message handler
/// \param object_factory_parameters: configuration parameters for the object
///   factory
/// \return Returns false if the _start method was generated correctly
bool generate_ansi_c_start_function(
  const symbolt &symbol,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  const c_object_factory_parameterst &object_factory_parameters)
{
  PRECONDITION(!symbol.value.is_nil());
  code_blockt init_code;

  // add 'HIDE' label
  init_code.add(code_labelt(CPROVER_PREFIX "HIDE", code_skipt()));

  // build call to initialization function

  {
    symbol_table_baset::symbolst::const_iterator init_it =
      symbol_table.symbols.find(INITIALIZE_FUNCTION);

    if(init_it==symbol_table.symbols.end())
    {
      messaget message(message_handler);
      message.error() << "failed to find " INITIALIZE_FUNCTION " symbol"
                      << messaget::eom;
      return true;
    }

    code_function_callt call_init(init_it->second.symbol_expr());
    call_init.add_source_location()=symbol.location;

    init_code.add(std::move(call_init));
  }

  // build call to main function

  code_function_callt call_main(symbol.symbol_expr());
  call_main.add_source_location()=symbol.location;
  call_main.function().add_source_location()=symbol.location;

  if(to_code_type(symbol.type).return_type() != void_type())
  {
    auxiliary_symbolt return_symbol;
    return_symbol.mode=ID_C;
    return_symbol.is_static_lifetime=false;
    return_symbol.name="return'";
    return_symbol.base_name = "return'";
    return_symbol.type=to_code_type(symbol.type).return_type();

    symbol_table.add(return_symbol);
    call_main.lhs()=return_symbol.symbol_expr();
  }

  const code_typet::parameterst &parameters=
    to_code_type(symbol.type).parameters();

  if(symbol.name==ID_main)
  {
    if(parameters.empty())
    {
      // ok
    }
    // The C standard (and any related architecture descriptions) enforces an
    // order of parameters. The user, however, may supply arbitrary
    // (syntactically valid) C code, even one that does not respect the calling
    // conventions set out in the C standard. If the user does supply such code,
    // then we can only tell them that they got it wrong, which is what we do
    // via the error message in the else branch of this code.
    else if(
      parameters.size() >= 2 && parameters[1].type().id() == ID_pointer &&
      (parameters.size() == 2 ||
       (parameters.size() == 3 && parameters[2].type().id() == ID_pointer)))
    {
      namespacet ns(symbol_table);

      {
        symbolt argc_symbol{"argc'", signed_int_type(), ID_C};
        argc_symbol.base_name = "argc'";
        argc_symbol.is_static_lifetime = true;
        argc_symbol.is_lvalue = true;

        auto r = symbol_table.insert(argc_symbol);
        if(!r.second && r.first != argc_symbol)
        {
          messaget message(message_handler);
          message.error() << "argc already exists but is not usable"
                          << messaget::eom;
          return true;
        }
      }

      const symbolt &argc_symbol = ns.lookup("argc'");

      {
        // we make the type of this thing an array of pointers
        // need to add one to the size -- the array is terminated
        // with NULL
        const exprt one_expr = from_integer(1, argc_symbol.type);
        const plus_exprt size_expr(argc_symbol.symbol_expr(), one_expr);
        const array_typet argv_type(pointer_type(char_type()), size_expr);

        symbolt argv_symbol{"argv'", argv_type, ID_C};
        argv_symbol.base_name = "argv'";
        argv_symbol.is_static_lifetime = true;
        argv_symbol.is_lvalue = true;

        auto r = symbol_table.insert(argv_symbol);
        if(!r.second && r.first != argv_symbol)
        {
          messaget message(message_handler);
          message.error() << "argv already exists but is not usable"
                          << messaget::eom;
          return true;
        }
      }

      const symbolt &argv_symbol=ns.lookup("argv'");
      const array_typet &argv_array_type = to_array_type(argv_symbol.type);

      {
        // Assume argc is at least zero. Note that we don't assume it's
        // at least one, since this isn't guaranteed, as exemplified by
        // https://www.qualys.com/2022/01/25/cve-2021-4034/pwnkit.txt
        // The C standard only guarantees "The value of argc shall be
        // nonnegative." and "argv[argc] shall be a null pointer."
        exprt zero = from_integer(0, argc_symbol.type);

        binary_relation_exprt ge(
          argc_symbol.symbol_expr(), ID_ge, std::move(zero));

        init_code.add(code_assumet(std::move(ge)));
      }

      if(config.ansi_c.max_argc.has_value())
      {
        exprt bound_expr =
          from_integer(*config.ansi_c.max_argc, argc_symbol.type);

        binary_relation_exprt le(
          argc_symbol.symbol_expr(), ID_le, std::move(bound_expr));

        init_code.add(code_assumet(std::move(le)));
      }

      // record argc as an input
      init_code.add(code_inputt{"argc", argc_symbol.symbol_expr()});

      if(parameters.size()==3)
      {
        {
          symbolt envp_size_symbol{"envp_size'", size_type(), ID_C};
          envp_size_symbol.base_name = "envp_size'";
          envp_size_symbol.is_static_lifetime = true;

          if(!symbol_table.insert(std::move(envp_size_symbol)).second)
          {
            messaget message(message_handler);
            message.error()
              << "failed to insert envp_size symbol" << messaget::eom;
            return true;
          }
        }

        const symbolt &envp_size_symbol=ns.lookup("envp_size'");

        {
          symbolt envp_symbol{
            "envp'",
            array_typet(
              pointer_type(char_type()), envp_size_symbol.symbol_expr()),
            ID_C};
          envp_symbol.base_name = "envp'";
          envp_symbol.is_static_lifetime = true;

          if(!symbol_table.insert(std::move(envp_symbol)).second)
          {
            messaget message(message_handler);
            message.error() << "failed to insert envp symbol" << messaget::eom;
            return true;
          }
        }

        // assume envp_size is INTMAX-1
        const mp_integer max =
          to_integer_bitvector_type(envp_size_symbol.type).largest();

        exprt max_minus_one=from_integer(max-1, envp_size_symbol.type);

        binary_relation_exprt le(
          envp_size_symbol.symbol_expr(), ID_le, std::move(max_minus_one));

        init_code.add(code_assumet(le));
      }

      {
        /* zero_string doesn't work yet */

        /*
        exprt zero_string(ID_zero_string, array_typet());
        zero_string.type().subtype()=char_type();
        zero_string.type().set(ID_size, "infinity");
        const index_exprt index(zero_string, from_integer(0, uint_type()));
        exprt address_of =
          typecast_exprt::conditional_cast(
            address_of_exprt(index, pointer_type(char_type())),
            argv_symbol.type.subtype());

        // assign argv[*] to the address of a string-object
        array_of_exprt array_of(address_of, argv_symbol.type);

        init_code.copy_to_operands(
          code_assignt(argv_symbol.symbol_expr(), array_of));
        */
      }

      {
        // assign argv[argc] to NULL
        const null_pointer_exprt null(
          to_pointer_type(argv_array_type.element_type()));

        index_exprt index_expr(
          argv_symbol.symbol_expr(),
          typecast_exprt::conditional_cast(
            argc_symbol.symbol_expr(), argv_array_type.index_type()));

        init_code.add(code_frontend_assignt(index_expr, null));
        // disable bounds check on that one
        init_code.statements().back().add_source_location().add_pragma(
          "disable:bounds-check");
      }

      if(parameters.size()==3)
      {
        const symbolt &envp_symbol=ns.lookup("envp'");
        const array_typet &envp_array_type = to_array_type(envp_symbol.type);
        const symbolt &envp_size_symbol=ns.lookup("envp_size'");

        // assume envp[envp_size] is NULL
        null_pointer_exprt null(
          to_pointer_type(envp_array_type.element_type()));

        index_exprt index_expr(
          envp_symbol.symbol_expr(),
          typecast_exprt::conditional_cast(
            envp_size_symbol.symbol_expr(), envp_array_type.index_type()));

        equal_exprt is_null(std::move(index_expr), std::move(null));

        init_code.add(code_assumet(is_null));
        // disable bounds check on that one
        init_code.statements().back().add_source_location().add_pragma(
          "disable:bounds-check");
      }

      {
        exprt::operandst &operands=call_main.arguments();

        if(parameters.size()==3)
          operands.resize(3);
        else
          operands.resize(2);

        exprt &op0=operands[0];
        exprt &op1=operands[1];

        op0 = typecast_exprt::conditional_cast(
          argc_symbol.symbol_expr(), parameters[0].type());

        {
          index_exprt index_expr(
            argv_symbol.symbol_expr(),
            from_integer(0, argv_array_type.index_type()));
          // disable bounds check on that one
          index_expr.add_source_location().add_pragma("disable:bounds-check");

          const pointer_typet &pointer_type =
            to_pointer_type(parameters[1].type());

          op1 = typecast_exprt::conditional_cast(
            address_of_exprt(index_expr), pointer_type);
        }

        // do we need envp?
        if(parameters.size()==3)
        {
          const symbolt &envp_symbol=ns.lookup("envp'");
          const array_typet &envp_array_type = to_array_type(envp_symbol.type);

          index_exprt index_expr(
            envp_symbol.symbol_expr(),
            from_integer(0, envp_array_type.index_type()));

          const pointer_typet &pointer_type =
            to_pointer_type(parameters[2].type());

          operands[2] = typecast_exprt::conditional_cast(
            address_of_exprt(index_expr), pointer_type);
        }
      }
    }
    else
    {
      const namespacet ns{symbol_table};
      const std::string main_signature = type2c(symbol.type, ns);
      messaget message(message_handler);
      message.error().source_location = symbol.location;
      message.error() << "'main' with signature '" << main_signature
                      << "' found,"
                      << " but expecting one of:\n"
                      << "   int main(void)\n"
                      << "   int main(int argc, char *argv[])\n"
                      << "   int main(int argc, char *argv[], char *envp[])\n"
                      << "If this is a non-standard main entry point please "
                         "provide a custom\n"
                      << "entry function and use --function instead"
                      << messaget::eom;
      return true;
    }
  }
  else
  {
    // produce nondet arguments
    call_main.arguments() = build_function_environment(
      parameters, init_code, symbol_table, object_factory_parameters);
  }

  init_code.add(std::move(call_main));

  // TODO: add read/modified (recursively in call graph) globals as INPUT/OUTPUT

  record_function_outputs(symbol, init_code, symbol_table);

  // now call destructor functions (a GCC extension)

  for(const auto &symbol_table_entry : symbol_table.symbols)
  {
    const symbolt &symbol = symbol_table_entry.second;

    if(symbol.type.id() != ID_code)
      continue;

    const code_typet &code_type = to_code_type(symbol.type);
    if(
      code_type.return_type().id() == ID_destructor &&
      code_type.parameters().empty())
    {
      code_function_callt destructor_call(symbol.symbol_expr());
      destructor_call.add_source_location() = symbol.location;
      init_code.add(std::move(destructor_call));
    }
  }

  // add the entry point symbol
  symbolt new_symbol{
    goto_functionst::entry_point(), code_typet{{}, void_type()}, symbol.mode};
  new_symbol.base_name = goto_functionst::entry_point();
  new_symbol.value.swap(init_code);

  if(!symbol_table.insert(std::move(new_symbol)).second)
  {
    messaget message(message_handler);
    message.error() << "failed to insert main symbol" << messaget::eom;
    return true;
  }

  return false;
}
