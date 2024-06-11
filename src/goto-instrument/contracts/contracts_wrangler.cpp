/*******************************************************************\

Module: Parse and annotate contracts from configuration files

Author: Qinheping Hu

Date: June 2023

\*******************************************************************/

/// \file
/// Parse and annotate contracts

#include "contracts_wrangler.h"

#include <util/c_types.h>
#include <util/expr_iterator.h>
#include <util/format_expr.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_types.h>

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

void contracts_wranglert::add_builtin_pointer_function_symbol(
  std::string function_name,
  const std::size_t num_of_args)
{
  // Already exist.
  if(symbol_table.has_symbol(CPROVER_PREFIX + function_name))
    return;

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
}

void contracts_wranglert::mangle(
  const loop_contracts_clauset &loop_contracts,
  const irep_idt &function_id)
{
  messaget log(message_handler);
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
  ansi_c_parser.parse();

  // Extract the invariants from prase_tree.
  exprt &inv_expr(static_cast<exprt &>(ansi_c_parser.parse_tree.items.front()
                                         .declarator()
                                         .value()
                                         .operands()[0]
                                         .add(ID_C_spec_loop_invariant))
                    .operands()[0]);

  log.debug() << "Extracted loop invariants: " << inv_expr.pretty() << "\n"
              << log.eom;

  // Extract the assigns from parse_tree.
  std::optional<exprt> assigns_expr;
  if(!loop_contracts.assigns.empty())
  {
    assigns_expr = static_cast<exprt &>(ansi_c_parser.parse_tree.items.front()
                                          .declarator()
                                          .value()
                                          .operands()[0]
                                          .add(ID_C_spec_assigns))
                     .operands()[0];
  }

  // Extract the decreases from parse_tree.
  exprt::operandst decreases_exprs;
  if(!loop_contracts.decreases.empty())
  {
    for(auto op : static_cast<exprt &>(ansi_c_parser.parse_tree.items.front()
                                         .declarator()
                                         .value()
                                         .operands()[0]
                                         .add(ID_C_spec_decreases))
                    .operands())
    {
      decreases_exprs.emplace_back(op);
    }
  }

  // Replace symbols in the clauses with the symbols in the symbol table.
  log.debug() << "Start to replace symbols" << log.eom;
  loop_contracts.replace_symbol(inv_expr);
  if(assigns_expr.has_value())
  {
    loop_contracts.replace_symbol(assigns_expr.value());
  }
  for(exprt &decrease_expr : decreases_exprs)
  {
    loop_contracts.replace_symbol(decrease_expr);
  }

  // Add builtin functions that might be used in contracts to the symbol table.
  add_builtin_pointer_function_symbol("loop_entry", 1);
  add_builtin_pointer_function_symbol("same_object", 2);
  add_builtin_pointer_function_symbol("OBJECT_SIZE", 1);
  add_builtin_pointer_function_symbol("POINTER_OBJECT", 1);
  add_builtin_pointer_function_symbol("POINTER_OFFSET", 1);

  // Typecheck clauses.
  ansi_c_typecheckt ansi_c_typecheck(
    ansi_c_parser.parse_tree,
    symbol_table,
    symbol_table.lookup_ref(function_id).module.c_str(),
    log.get_message_handler());

  // Typecheck and annotate invariants.
  {
    log.debug() << "Start to typecheck invariants." << log.eom;
    ansi_c_typecheck.typecheck_expr(inv_expr);
    if(has_subexpr(inv_expr, ID_old))
      throw invalid_input_exceptiont(CPROVER_PREFIX
                                     "old is not allowed in loop invariants.");

    invariant_mapt inv_map;
    inv_map[loop_idt(function_id, std::stoi(loop_contracts.identifier))] =
      and_exprt(simplify_expr(inv_expr, ns), true_exprt());
    annotate_invariants(inv_map, goto_model);
  }

  // Typecheck and annotate assigns.
  log.debug() << "Start to typecheck assigns." << log.eom;
  if(assigns_expr.has_value())
  {
    ansi_c_typecheck.typecheck_spec_assigns(assigns_expr.value().operands());

    invariant_mapt assigns_map;
    assigns_map[loop_idt(function_id, std::stoi(loop_contracts.identifier))] =
      assigns_expr.value();
    annotate_assigns(assigns_map, goto_model);
  }

  // Typecheck an annotate decreases.
  log.debug() << "Start to typecheck decreases." << log.eom;
  if(!decreases_exprs.empty())
  {
    std::map<loop_idt, std::vector<exprt>> decreases_map;
    decreases_map[loop_idt(function_id, std::stoi(loop_contracts.identifier))] =
      std::vector<exprt>();
    for(exprt &decrease_expr : decreases_exprs)
    {
      ansi_c_typecheck.typecheck_expr(decrease_expr);
      decreases_map[loop_idt(function_id, std::stoi(loop_contracts.identifier))]
        .emplace_back(decrease_expr);
    }
    annotate_decreases(decreases_map, goto_model);
  }

  log.debug() << "Mangling finished." << log.eom;
  // Remove added symbol.
  symbol_table.remove(CPROVER_PREFIX "loop_entry");
  symbol_table.remove(CPROVER_PREFIX "same_object");
  symbol_table.remove(CPROVER_PREFIX "OBJECT_SIZE");
  symbol_table.remove(CPROVER_PREFIX "POINTER_OBJECT");
  symbol_table.remove(CPROVER_PREFIX "POINTER_OFFSET");
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

        if(invariants_str.empty())
        {
          throw deserialization_exceptiont(
            "loop entry must have one invariant string");
        }

        function_config.loop_contracts.emplace_back(
          loop_id, invariants_str, assigns_str, decreases_str, replace_symbol);
      }
    }
  }
}
