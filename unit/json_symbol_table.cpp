/// Author: Daniel Poetzl

/// \file json symbol table read/write consistency

#include <ansi-c/ansi_c_language.h>

#include <cbmc/cbmc_parse_options.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/show_symbol_table.h>

#include <json-symtab-language/json_symbol_table.h>
#include <json/json_parser.h>

#include <langapi/language_file.h>
#include <langapi/mode.h>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/message.h>
#include <util/options.h>
#include <util/symbol_table.h>

#include <testing-utils/catch.hpp>
#include <testing-utils/message.h>

#include <iosfwd>

class test_ui_message_handlert : public ui_message_handlert
{
public:
  explicit test_ui_message_handlert(std::ostream &out)
    : ui_message_handlert(cmdlinet(), ""), json_stream_array(out, 0)
  {
  }

  uit get_ui() const
  {
    return uit::JSON_UI;
  }

  json_stream_arrayt &get_json_stream()
  {
    return json_stream_array;
  }

  json_stream_arrayt json_stream_array;
};

void get_goto_model(std::istream &in, goto_modelt &goto_model)
{
  optionst options;
  cbmc_parse_optionst::set_default_options(options);

  messaget null_message(null_message_handler);

  language_filest language_files;
  language_files.set_message_handler(null_message_handler);

  std::string filename("");

  language_filet &language_file = language_files.add_file(filename);

  language_file.language = get_default_language();

  languaget &language = *language_file.language;
  language.set_message_handler(null_message_handler);
  language.set_language_options(options);

  {
    bool r = language.parse(in, filename);
    REQUIRE(!r);
  }

  language_file.get_modules();

  {
    bool r = language_files.typecheck(goto_model.symbol_table);
    REQUIRE(!r);
  }

  REQUIRE(!goto_model.symbol_table.has_symbol(goto_functionst::entry_point()));

  {
    bool r = language_files.generate_support_functions(goto_model.symbol_table);
    REQUIRE(!r);
  }

  goto_convert(
    goto_model.symbol_table, goto_model.goto_functions, null_message_handler);
}

TEST_CASE("json symbol table read/write consistency")
{
  register_language(new_ansi_c_language);

  cmdlinet cmdline;
  config.main = "main";
  config.set(cmdline);

  goto_modelt goto_model;

  // Get symbol table associated with goto program

  {
    std::string program = "int main() { return 0; }\n";

    std::istringstream in(program);
    get_goto_model(in, goto_model);
  }

  const symbol_tablet &symbol_table1 = goto_model.symbol_table;

  // Convert symbol table to json string

  std::ostringstream out;

  {
    test_ui_message_handlert ui_message_handler(out);
    REQUIRE(ui_message_handler.get_ui() == ui_message_handlert::uit::JSON_UI);

    show_symbol_table(symbol_table1, ui_message_handler);
  }

  // Convert json string to symbol table

  symbol_tablet symbol_table2;

  {
    std::istringstream in(out.str());
    jsont json;

    bool r = parse_json(in, "", null_message_handler, json);
    REQUIRE(!r);

    REQUIRE(json.is_array());

    const json_arrayt &json_array = to_json_array(json);
    const jsont &json_symbol_table = *json_array.begin();

    symbol_table_from_json(json_symbol_table, symbol_table2);
  }

  // Finally check if symbol tables are consistent

  REQUIRE(symbol_table1 == symbol_table2);
}
