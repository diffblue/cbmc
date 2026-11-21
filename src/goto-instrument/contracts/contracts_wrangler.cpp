/*******************************************************************\

Module: Parse and annotate contracts from configuration files

Author: Qinheping Hu

Date: June 2023

\*******************************************************************/

/// \file
/// Parse and annotate contracts

#include "contracts_wrangler.h"

#include <util/c_types.h>
#include <util/exception_utils.h>
#include <util/expr_iterator.h>
#include <util/format_expr.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/string2int.h>
#include <util/typecheck.h>

#include <goto-programs/remove_unused_functions.h>

#include <ansi-c/ansi_c_parser.h>
#include <ansi-c/ansi_c_typecheck.h>
#include <goto-instrument/contracts/utils.h>

contracts_wranglert::contracts_wranglert(
  goto_modelt &goto_model,
  const std::string &file_name,
  message_handlert &message_handler)
  : ns(goto_model.symbol_table),
    goto_model(goto_model),
    symbol_table(goto_model.symbol_table),
    goto_functions(goto_model.goto_functions),
    message_handler(message_handler)
{
  jsont configuration;

  if(parse_json(file_name, message_handler, configuration))
    throw deserialization_exceptiont(file_name + " is not a valid JSON file");

  configure_functions(configuration);

  // Mangle loop contracts function by function.
  // We match function with a regex. There should one and only one function
  // with name matched by the regex.
  for(const auto &function_entry : this->functions)
  {
    bool function_found = false;

    for(const auto &function : goto_model.goto_functions.function_map)
    {
      // We find a matched function.
      if(std::regex_match(function.first.c_str(), function_entry.first))
      {
        if(function_found)
          throw deserialization_exceptiont(
            "function regex " + function_entry.second.regex_str +
            " matches more than one function");

        function_found = true;

        // Mangle all loop contracts in the function.
        for(const auto &loop_entry : function_entry.second.loop_contracts)
        {
          mangle(loop_entry, function.first);
        }
      }
    }

    if(!function_found)
      throw deserialization_exceptiont(
        "function regex " + function_entry.second.regex_str +
        " matches no function");
  }
}

std::optional<irep_idt>
contracts_wranglert::add_builtin_pointer_function_symbol(
  std::string function_name,
  const std::size_t num_of_args)
{
  // Already exist.
  if(symbol_table.has_symbol(CPROVER_PREFIX + function_name))
    return {};

  code_typet::parameterst parameters;
  for(unsigned i = 0; i < num_of_args; i++)
  {
    parameters.emplace_back(pointer_type(void_type()));
  }
  symbolt fun_symbol(
    CPROVER_PREFIX + function_name,
    code_typet(parameters, empty_typet()),
    ID_C);
  symbol_table.add(fun_symbol);
  return fun_symbol.name;
}

/// Explain why \p function has no natural loop numbered \p loop_number that
/// loop contracts can be attached to.
static std::string
describe_missing_loop(goto_functiont &function, const unsigned loop_number)
{
  for(auto it = function.body.instructions.begin();
      it != function.body.instructions.end();
      ++it)
  {
    if(!it->is_backwards_goto() || it->loop_number != loop_number)
      continue;

    if(it->get_target() == it)
    {
      return "consists of a single instruction that jumps to itself, which "
             "loop contracts do not support";
    }

    // A loop head with several back edges forms a single natural loop, which
    // is numbered by its last back edge.
    for(auto other = std::next(it); other != function.body.instructions.end();
        ++other)
    {
      if(other->is_backwards_goto() && other->get_target() == it->get_target())
      {
        const auto loop = find_loop_head_and_end(other->loop_number, function);
        if(loop.has_value())
        {
          return "is not the last back edge to its loop head; contracts for "
                 "this loop must be given for loop " +
                 std::to_string(loop->second->loop_number);
        }
      }
    }

    return "is not a natural loop";
  }

  return "does not exist";
}

void contracts_wranglert::mangle(
  const loop_contracts_clauset &loop_contracts,
  const irep_idt &function_id)
{
  messaget log(message_handler);

  const std::string loop_description =
    "loop " + std::to_string(loop_contracts.loop_number) + " of function " +
    id2string(function_id);

  auto function_it = goto_model.goto_functions.function_map.find(function_id);
  PRECONDITION(function_it != goto_model.goto_functions.function_map.end());
  const auto loop =
    find_loop_head_and_end(loop_contracts.loop_number, function_it->second);
  if(!loop.has_value())
  {
    throw invalid_input_exceptiont{
      loop_description + ", as given in the loop contracts file, " +
      describe_missing_loop(function_it->second, loop_contracts.loop_number)};
  }
  const goto_programt::targett loop_end = loop->second;

  // Loop contracts mangling consists of four steps.
  //
  // 1. Construct a fake function with a fake loop that contains the loop
  //    contracts for parsing the contracts.
  // 2. Parse the fake function and extract the contracts as exprt.
  // 3. Replace symbols in the extracted exprt with the symbols in the
  //    symbol table of the goto model according to the symbol map provided by
  //    the user.
  // 4. Typecheck all contracts exprt.
  // 5. Annotate all contracts exprt to the corresponding loop.

  // Construct a fake function to parse.
  // void function_id()
  // {
  //    while(1==1)
  //    __CPROVER_assigns(assigns_str) // optional
  //    __CPROVER_loop_invariant(invariants_str)
  //    __CPROVER_decreases(decreases_str) // optional
  // }
  std::ostringstream pr;
  pr << "void _fn() { while(1==1)";
  if(!loop_contracts.assigns.empty())
  {
    pr << CPROVER_PREFIX << "assigns(" << loop_contracts.assigns << ") ";
  }
  pr << CPROVER_PREFIX << "loop_invariant(" << loop_contracts.invariants
     << ") ";
  if(!loop_contracts.decreases.empty())
  {
    pr << CPROVER_PREFIX << "decreases(" << loop_contracts.decreases << ") ";
  }
  pr << " {}}" << std::endl;

  log.debug() << "Constructing fake function:\n" << pr.str() << log.eom;

  // Parse the fake function.
  std::istringstream is(pr.str());
  ansi_c_parsert ansi_c_parser{message_handler};
  ansi_c_parser.set_line_no(0);
  ansi_c_parser.set_file("<predicate>");
  ansi_c_parser.in = &is;
  ansi_c_parser.for_has_scope = config.ansi_c.for_has_scope;
  ansi_c_parser.ts_18661_3_Floatn_types = config.ansi_c.ts_18661_3_Floatn_types;
  ansi_c_parser.__float128_is_keyword = config.ansi_c.__float128_is_keyword;
  ansi_c_parser.float16_type = config.ansi_c.float16_type;
  ansi_c_parser.bf16_type = config.ansi_c.bf16_type;
  ansi_c_parser.fp16_type = config.ansi_c.fp16_type;
  ansi_c_parser.cpp98 = false; // it's not C++
  ansi_c_parser.cpp11 = false; // it's not C++
  ansi_c_parser.mode = config.ansi_c.mode;
  ansi_c_scanner_init(ansi_c_parser);

  // The clauses are user input: a syntax error leaves the parse tree empty,
  // which must be reported rather than dereferenced.
  if(ansi_c_parser.parse() || ansi_c_parser.parse_tree.items.empty())
  {
    throw invalid_input_exceptiont{
      "failed to parse the loop contracts for " + loop_description +
      " given in the loop contracts file"};
  }

  // The loop of the fake function, which carries the clauses.
  codet &fake_loop = static_cast<codet &>(
    ansi_c_parser.parse_tree.items.front().declarator().value().operands()[0]);
  // As in the C front-end, decide from the parse tree which clauses are given.
  // Note that add() would create an empty (non-nil) clause.
  const bool has_assigns = fake_loop.find(ID_C_spec_assigns).is_not_nil();
  const bool has_decreases = fake_loop.find(ID_C_spec_decreases).is_not_nil();

  // Replace symbols in the clauses with the symbols in the symbol table.
  log.debug() << "Start to replace symbols" << log.eom;
  loop_contracts.replace_symbol(
    static_cast<exprt &>(fake_loop.add(ID_C_spec_loop_invariant)));
  if(has_assigns)
    loop_contracts.replace_symbol(
      static_cast<exprt &>(fake_loop.add(ID_C_spec_assigns)));
  if(has_decreases)
    loop_contracts.replace_symbol(
      static_cast<exprt &>(fake_loop.add(ID_C_spec_decreases)));

  // Add builtin functions that might be used in contracts to the symbol table,
  // and remove them again when leaving this function, also via an exception.
  struct remove_symbols_on_exitt
  {
    symbol_tablet &symbol_table;
    std::vector<irep_idt> names;
    ~remove_symbols_on_exitt()
    {
      for(const auto &name : names)
        symbol_table.remove(name);
    }
  } added_symbols{symbol_table, {}};
  for(const auto &builtin : std::vector<std::pair<std::string, std::size_t>>{
        {"loop_entry", 1},
        {"same_object", 2},
        {"OBJECT_SIZE", 1},
        {"POINTER_OBJECT", 1},
        {"POINTER_OFFSET", 1}})
  {
    if(
      const auto added =
        add_builtin_pointer_function_symbol(builtin.first, builtin.second))
    {
      added_symbols.names.push_back(*added);
    }
  }

  // Typecheck the clauses as the C front-end does for loop contracts given in
  // the source code: this converts the invariant to Boolean and the
  // components of the decreases clause to arithmetic types, and rejects
  // __CPROVER_old in the invariant.  The type checker reports errors via the
  // message handler and then throws.
  ansi_c_typecheckt ansi_c_typecheck(
    ansi_c_parser.parse_tree,
    symbol_table,
    symbol_table.lookup_ref(function_id).module.c_str(),
    log.get_message_handler());

  const auto typecheck_error = [&loop_description]()
  {
    return invalid_input_exceptiont{
      "failed to typecheck the loop contracts for " + loop_description +
      " given in the loop contracts file"};
  };

  // The same exceptions as typecheckt::typecheck_main handles.
  try
  {
    log.debug() << "Start to typecheck the clauses." << log.eom;
    ansi_c_typecheck.typecheck_spec_loop_invariant(fake_loop);
    if(has_assigns)
    {
      ansi_c_typecheck.typecheck_spec_assigns(
        static_cast<unary_exprt &>(fake_loop.add(ID_C_spec_assigns))
          .op()
          .operands());
    }
    ansi_c_typecheck.typecheck_spec_decreases(fake_loop);
  }
  catch(int)
  {
    throw typecheck_error();
  }
  catch(const char *e)
  {
    log.error() << e << messaget::eom;
    throw typecheck_error();
  }
  catch(const std::string &e)
  {
    log.error() << e << messaget::eom;
    throw typecheck_error();
  }
  catch(const typecheckt::errort &e)
  {
    if(!e.what().empty())
    {
      log.error().source_location = e.source_location();
      log.error() << e.what() << messaget::eom;
    }
    throw typecheck_error();
  }
  catch(const invalid_source_file_exceptiont &e)
  {
    log.error().source_location = e.get_source_location();
    log.error() << e.reason() << messaget::eom;
    throw typecheck_error();
  }

  // Annotate the invariant. The clause may consist of several invariants, as
  // in "i <= 8) __CPROVER_loop_invariant(i >= 0", all of which must hold.
  const exprt::operandst &invariants =
    static_cast<const exprt &>(fake_loop.find(ID_C_spec_loop_invariant))
      .operands();
  const exprt inv_expr = simplify_expr(conjunction(invariants), ns);
  log.debug() << "Extracted loop invariants: " << inv_expr.pretty() << "\n"
              << log.eom;
  loop_end->condition_nonconst().add(ID_C_spec_loop_invariant) =
    and_exprt{inv_expr, true_exprt{}};

  // Annotate the assigns clause.
  if(has_assigns)
  {
    loop_end->condition_nonconst().add(ID_C_spec_assigns) =
      static_cast<const exprt &>(fake_loop.find(ID_C_spec_assigns))
        .operands()[0];
  }

  // Annotate the decreases clause.
  if(has_decreases)
  {
    exprt decreases{ID_target_list};
    decreases.operands() =
      static_cast<const exprt &>(fake_loop.find(ID_C_spec_decreases))
        .operands();
    loop_end->condition_nonconst().add(ID_C_spec_decreases) = decreases;
  }

  log.debug() << "Mangling finished." << log.eom;
}

void contracts_wranglert::configure_functions(const jsont &config)
{
  auto functions = config["functions"];

  if(functions.is_null())
    return;

  if(!functions.is_array())
    throw deserialization_exceptiont("functions entry must be sequence");

  for(const auto &function : to_json_array(functions))
  {
    if(!function.is_object())
      throw deserialization_exceptiont("function entry must be object");

    for(const auto &function_entry : to_json_object(function))
    {
      const auto function_name = function_entry.first;
      const auto &items = function_entry.second;

      if(!items.is_array())
        throw deserialization_exceptiont("loops entry must be sequence");

      this->functions.emplace_back(function_name, functiont{});
      functiont &function_config = this->functions.back().second;
      function_config.regex_str = function_name;

      for(const auto &function_item : to_json_array(items))
      {
        if(!function_item.is_object())
          throw deserialization_exceptiont("loop entry must be object");

        std::string loop_id = "";
        std::string invariants_str = "";
        std::string assigns_str = "";
        std::string decreases_str = "";
        unchecked_replace_symbolt replace_symbol;

        for(const auto &loop_item : to_json_object(function_item))
        {
          if(!loop_item.second.is_string())
            throw deserialization_exceptiont("loop item must be string");

          if(loop_item.first == "loop_id")
          {
            loop_id = loop_item.second.value;
            continue;
          }

          if(loop_item.first == "assigns")
          {
            assigns_str = loop_item.second.value;
            continue;
          }

          if(loop_item.first == "decreases")
          {
            decreases_str = loop_item.second.value;
            continue;
          }

          if(loop_item.first == "invariants")
          {
            invariants_str = loop_item.second.value;
            continue;
          }

          if(loop_item.first == "symbol_map")
          {
            std::string symbol_map_str = loop_item.second.value;

            // Remove all space in symbol_map_str
            symbol_map_str.erase(
              std::remove_if(
                symbol_map_str.begin(), symbol_map_str.end(), isspace),
              symbol_map_str.end());

            for(const auto &symbol_map_entry :
                split_string(symbol_map_str, ';'))
            {
              const auto symbol_map_pair = split_string(symbol_map_entry, ',');
              const auto &symbol = symbol_table.lookup(symbol_map_pair.back());
              if(symbol == nullptr)
                throw deserialization_exceptiont(
                  "symbol with id \"" + symbol_map_pair.front() +
                  "\" does not exist in the symbol table");
              // Create a dummy symbol. The type will be discarded when inserted
              // into replace_symbol.
              const symbol_exprt old_expr(
                symbol_map_pair.front(), bool_typet());
              replace_symbol.insert(old_expr, symbol->symbol_expr());
            }

            continue;
          }

          throw deserialization_exceptiont("unexpected loop item");
        }

        if(loop_id.empty())
        {
          throw deserialization_exceptiont(
            "loop entry must have one identifier");
        }

        // Surrounding white space is permitted, as in the symbol map.
        const auto first = loop_id.find_first_not_of(" \t\n\r");
        const auto last = loop_id.find_last_not_of(" \t\n\r");
        const std::optional<unsigned> loop_number =
          first == std::string::npos
            ? std::optional<unsigned>{}
            : string2optional_unsigned(loop_id.substr(first, last - first + 1));
        if(!loop_number.has_value())
        {
          throw deserialization_exceptiont(
            "loop identifier '" + loop_id + "' of function " + function_name +
            " given in the loop contracts file is not a loop number");
        }

        if(invariants_str.empty())
        {
          throw deserialization_exceptiont(
            "loop entry must have one invariant string");
        }

        function_config.loop_contracts.emplace_back(
          *loop_number,
          invariants_str,
          assigns_str,
          decreases_str,
          replace_symbol);
      }
    }
  }
}
