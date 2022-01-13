/*******************************************************************\

Module: Linker Script Merging

Author: Kareem Khazem <karkhaz@karkhaz.com>, 2017

\*******************************************************************/

#include "linker_script_merge.h"

#include <algorithm>
#include <fstream>
#include <iterator>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/expr_initializer.h>
#include <util/magic.h>
#include <util/pointer_expr.h>
#include <util/run.h>
#include <util/tempfile.h>

#include <json/json_parser.h>

#include <linking/static_lifetime_init.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/read_goto_binary.h>

#include "compile.h"

int linker_script_merget::add_linker_script_definitions()
{
  if(!cmdline.isset('T'))
    return 0;

  auto original_goto_model =
    read_goto_binary(goto_binary, log.get_message_handler());

  if(!original_goto_model.has_value())
  {
    log.error() << "Unable to read goto binary for linker script merging"
                << messaget::eom;
    return 1;
  }

  temporary_filet linker_def_outfile("goto-cc-linker-info", ".json");
  std::list<irep_idt> linker_defined_symbols;
  int fail = get_linker_script_data(
    linker_defined_symbols,
    original_goto_model->symbol_table,
    elf_binary,
    linker_def_outfile());
  // ignore linker script parsing failures until the code is tested more widely
  if(fail!=0)
    return 0;

  jsont data;
  fail = parse_json(linker_def_outfile(), log.get_message_handler(), data);
  if(fail!=0)
  {
    log.error() << "Problem parsing linker script JSON data" << messaget::eom;
    return fail;
  }

  fail=linker_data_is_malformed(data);
  if(fail!=0)
  {
    log.error() << "Malformed linker-script JSON document" << messaget::eom;
    data.output(log.error());
    return fail;
  }

  linker_valuest linker_values;
  fail = ls_data2instructions(
    data,
    cmdline.get_value('T'),
    original_goto_model->symbol_table,
    linker_values);
  if(fail!=0)
  {
    log.error() << "Could not add linkerscript defs to symbol table"
                << messaget::eom;
    return fail;
  }
  if(
    original_goto_model->goto_functions.function_map.erase(
      INITIALIZE_FUNCTION) != 0)
  {
    static_lifetime_init(
      original_goto_model->symbol_table,
      original_goto_model->symbol_table.lookup_ref(INITIALIZE_FUNCTION)
        .location);
    goto_convert(
      INITIALIZE_FUNCTION,
      original_goto_model->symbol_table,
      original_goto_model->goto_functions,
      log.get_message_handler());
    original_goto_model->goto_functions.update();
  }

  fail=goto_and_object_mismatch(linker_defined_symbols, linker_values);
  if(fail!=0)
    return fail;

  // The keys of linker_values are exactly the elements of
  // linker_defined_symbols, so iterate over linker_values from now on.

  fail = pointerize_linker_defined_symbols(*original_goto_model, linker_values);

  if(fail!=0)
  {
    log.error() << "Could not pointerize all linker-defined expressions"
                << messaget::eom;
    return fail;
  }

  fail = compilet::write_bin_object_file(
    goto_binary,
    *original_goto_model,
    cmdline.isset("validate-goto-model"),
    log.get_message_handler());

  if(fail!=0)
  {
    log.error() << "Could not write linkerscript-augmented binary"
                << messaget::eom;
  }

  return fail;
}

linker_script_merget::linker_script_merget(
  const std::string &elf_binary,
  const std::string &goto_binary,
  const cmdlinet &cmdline,
  message_handlert &message_handler)
  : elf_binary(elf_binary),
    goto_binary(goto_binary),
    cmdline(cmdline),
    log(message_handler),
    replacement_predicates(
      {replacement_predicatet(
         "address of array's first member",
         [](const exprt &expr) -> const symbol_exprt & {
           return to_symbol_expr(
             to_index_expr(to_address_of_expr(expr).object()).index());
         },
         [](const exprt &expr) {
           return expr.id() == ID_address_of &&
                  expr.type().id() == ID_pointer &&

                  to_address_of_expr(expr).object().id() == ID_index &&
                  to_address_of_expr(expr).object().type().id() ==
                    ID_unsignedbv &&

                  to_index_expr(to_address_of_expr(expr).object())
                      .array()
                      .id() == ID_symbol &&
                  to_index_expr(to_address_of_expr(expr).object())
                      .array()
                      .type()
                      .id() == ID_array &&

                  to_index_expr(to_address_of_expr(expr).object())
                      .index()
                      .id() == ID_constant &&
                  to_index_expr(to_address_of_expr(expr).object())
                      .index()
                      .type()
                      .id() == ID_signedbv;
         }),
       replacement_predicatet(
         "address of array",
         [](const exprt &expr) -> const symbol_exprt & {
           return to_symbol_expr(to_address_of_expr(expr).object());
         },
         [](const exprt &expr) {
           return expr.id() == ID_address_of &&
                  expr.type().id() == ID_pointer &&

                  to_address_of_expr(expr).object().id() == ID_symbol &&
                  to_address_of_expr(expr).object().type().id() == ID_array;
         }),
       replacement_predicatet(
         "address of struct",
         [](const exprt &expr) -> const symbol_exprt & {
           return to_symbol_expr(to_address_of_expr(expr).object());
         },
         [](const exprt &expr) {
           return expr.id() == ID_address_of &&
                  expr.type().id() == ID_pointer &&

                  to_address_of_expr(expr).object().id() == ID_symbol &&
                  (to_address_of_expr(expr).object().type().id() == ID_struct ||
                   to_address_of_expr(expr).object().type().id() ==
                     ID_struct_tag);
         }),
       replacement_predicatet(
         "array variable",
         [](const exprt &expr) -> const symbol_exprt & {
           return to_symbol_expr(expr);
         },
         [](const exprt &expr) {
           return expr.id() == ID_symbol && expr.type().id() == ID_array;
         }),
       replacement_predicatet(
         "pointer (does not need pointerizing)",
         [](const exprt &expr) -> const symbol_exprt & {
           return to_symbol_expr(expr);
         },
         [](const exprt &expr) {
           return expr.id() == ID_symbol && expr.type().id() == ID_pointer;
         })})
{}

int linker_script_merget::pointerize_linker_defined_symbols(
  goto_modelt &goto_model,
  const linker_valuest &linker_values)
{
  const namespacet ns(goto_model.symbol_table);

  int ret=0;

  // Next, find all occurrences of linker-defined symbols that are _values_
  // of some symbol in the symbol table, and pointerize them too
  for(const auto &pair : goto_model.symbol_table.symbols)
  {
    std::list<symbol_exprt> to_pointerize;
    symbols_to_pointerize(linker_values, pair.second.value, to_pointerize);

    if(to_pointerize.empty())
      continue;
    log.debug() << "Pointerizing the symbol-table value of symbol "
                << pair.first << messaget::eom;
    int fail = pointerize_subexprs_of(
      goto_model.symbol_table.get_writeable_ref(pair.first).value,
      to_pointerize,
      linker_values);
    if(to_pointerize.empty() && fail==0)
      continue;
    ret=1;
    for(const auto &sym : to_pointerize)
    {
      log.error() << " Could not pointerize '" << sym.get_identifier()
                  << "' in symbol table entry " << pair.first << ". Pretty:\n"
                  << sym.pretty() << "\n";
    }
    log.error() << messaget::eom;
  }

  // Finally, pointerize all occurrences of linker-defined symbols in the
  // goto program
  for(auto &gf : goto_model.goto_functions.function_map)
  {
    goto_programt &program=gf.second.body;
    for(auto &instruction : program.instructions)
    {
      for(exprt *insts : std::list<exprt *>(
            {&(instruction.code_nonconst()), &(instruction.guard)}))
      {
        std::list<symbol_exprt> to_pointerize;
        symbols_to_pointerize(linker_values, *insts, to_pointerize);
        if(to_pointerize.empty())
          continue;
        log.debug() << "Pointerizing a program expression..." << messaget::eom;
        int fail = pointerize_subexprs_of(*insts, to_pointerize, linker_values);
        if(to_pointerize.empty() && fail==0)
          continue;
        ret=1;
        for(const auto &sym : to_pointerize)
        {
          log.error() << " Could not pointerize '" << sym.get_identifier()
                      << "' in function " << gf.first << ". Pretty:\n"
                      << sym.pretty() << "\n";
          log.error().source_location = instruction.source_location();
        }
        log.error() << messaget::eom;
      }
    }
  }
  return ret;
}

int linker_script_merget::replace_expr(
    exprt &old_expr,
    const linker_valuest &linker_values,
    const symbol_exprt &old_symbol,
    const irep_idt &ident,
    const std::string &shape)
{
  auto it=linker_values.find(ident);
  if(it==linker_values.end())
  {
    log.error() << "Could not find a new expression for linker script-defined "
                << "symbol '" << ident << "'" << messaget::eom;
    return 1;
  }
  symbol_exprt new_expr=it->second.first;
  new_expr.add_source_location()=old_symbol.source_location();
  log.debug() << "Pointerizing linker-defined symbol '" << ident
              << "' of shape <" << shape << ">." << messaget::eom;
  old_expr=new_expr;
  return 0;
}

int linker_script_merget::pointerize_subexprs_of(
  exprt &expr,
  std::list<symbol_exprt> &to_pointerize,
  const linker_valuest &linker_values)
{
  int fail=0, tmp=0;
  for(auto const &pair : linker_values)
    for(auto const &pattern : replacement_predicates)
    {
      if(!pattern.match(expr))
        continue;
      // take a copy, expr will be changed below
      const symbol_exprt inner_symbol=pattern.inner_symbol(expr);
      if(pair.first!=inner_symbol.get_identifier())
        continue;
      tmp=replace_expr(expr, linker_values, inner_symbol, pair.first,
          pattern.description());
      fail=tmp?tmp:fail;
      auto result=std::find(to_pointerize.begin(), to_pointerize.end(),
          inner_symbol);
      if(result==to_pointerize.end())
      {
        fail=1;
        log.error() << "Too many removals of '" << inner_symbol.get_identifier()
                    << "'" << messaget::eom;
      }
      else
        to_pointerize.erase(result);
      // If we get here, we've just pointerized this expression. That expression
      // will be a symbol possibly wrapped in some unary junk, but won't contain
      // other symbols as subexpressions that might need to be pointerized. So
      // it's safe to bail out here.
      return fail;
    }

  for(auto &op : expr.operands())
  {
    tmp = pointerize_subexprs_of(op, to_pointerize, linker_values);
    fail=tmp?tmp:fail;
  }
  return fail;
}

void linker_script_merget::symbols_to_pointerize(
    const linker_valuest &linker_values,
    const exprt &expr,
    std::list<symbol_exprt> &to_pointerize) const
{
  for(const auto &op : expr.operands())
  {
    if(op.id()!=ID_symbol)
      continue;
    const symbol_exprt &sym_exp=to_symbol_expr(op);
    const auto &pair=linker_values.find(sym_exp.get_identifier());
    if(pair!=linker_values.end())
        to_pointerize.push_back(sym_exp);
  }
  for(const auto &op : expr.operands())
    symbols_to_pointerize(linker_values, op, to_pointerize);
}

#if 0
The current implementation of this function is less precise than the
  commented-out version below. To understand the difference between these
  implementations, consider the following example:

Suppose we have a section in the linker script, 100 bytes long, where the
address of the symbol sec_start is the start of the section (value 4096) and the
address of sec_end is the end of that section (value 4196).

The current implementation synthesizes the goto-version of the following C:

    char __sec_array[100];
    char *sec_start=(&__sec_array[0]);
    char *sec_end=((&__sec_array[0])+100);
      // Yes, it is 100 not 99. We're pointing to the end of the memory occupied
      // by __sec_array, not the last element of __sec_array.

This is imprecise for the following reason: the actual address of the array and
the pointers shall be some random CBMC-internal address, instead of being 4096
and 4196. The linker script, on the other hand, would have specified the exact
position of the section, and we even know what the actual values of sec_start
and sec_end are from the object file (these values are in the `addresses` list
of the `data` argument to this function). If the correctness of the code depends
on these actual values, then CBMCs model of the code is too imprecise to verify
this.

The commented-out version of this function below synthesizes the following:

    char *sec_start=4096;
    char *sec_end=4196;
    __CPROVER_allocated_memory(4096, 100);

This code has both the actual addresses of the start and end of the section and
tells CBMC that the intermediate region is valid. However, the allocated_memory
macro does not currently allocate an actual object at the address 4096, so
symbolic execution can fail. In particular, the 'allocated memory' is part of
__CPROVER_memory, which does not have a bounded size; this means that (for
example) calls to memcpy or memset fail, because the first and third arguments
do not have know n size. The commented-out implementation should be reinstated
once this limitation of __CPROVER_allocated_memory has been fixed.

In either case, no other changes to the rest of the code (outside this function)
should be necessary. The rest of this file converts expressions containing the
linker-defined symbol into pointer types if they were not already, and this is
the right behaviour for both implementations.
#endif
int linker_script_merget::ls_data2instructions(
    jsont &data,
    const std::string &linker_script,
    symbol_tablet &symbol_table,
    linker_valuest &linker_values)
#if 1
{
  std::map<irep_idt, std::size_t> truncated_symbols;
  for(auto &d : to_json_array(data["regions"]))
  {
    bool has_end=d["has-end-symbol"].is_true();

    std::ostringstream array_name;
    array_name << CPROVER_PREFIX << "linkerscript-array_"
      << d["start-symbol"].value;
    if(has_end)
      array_name << "-" << d["end-symbol"].value;


    // Array symbol_exprt
    mp_integer array_size = string2integer(d["size"].value);
    if(array_size > MAX_FLATTENED_ARRAY_SIZE)
    {
      log.warning() << "Object section '" << d["section"].value << "' of size "
                    << array_size << " is too large to model. Truncating to "
                    << MAX_FLATTENED_ARRAY_SIZE << " bytes" << messaget::eom;
      array_size=MAX_FLATTENED_ARRAY_SIZE;
      if(!has_end)
        truncated_symbols[d["size-symbol"].value]=MAX_FLATTENED_ARRAY_SIZE;
    }

    constant_exprt    array_size_expr=from_integer(array_size, size_type());
    array_typet       array_type(char_type(), array_size_expr);

    source_locationt array_loc;
    array_loc.set_file(linker_script);
    std::ostringstream array_comment;
    array_comment << "Object section '" << d["section"].value << "' of size "
                  << array_size << " bytes";
    array_loc.set_comment(array_comment.str());

    namespacet ns(symbol_table);
    const auto zi = zero_initializer(array_type, array_loc, ns);
    CHECK_RETURN(zi.has_value());

    // Add the array to the symbol table.
    symbolt array_sym;
    array_sym.is_static_lifetime = true;
    array_sym.is_lvalue = true;
    array_sym.is_state_var = true;
    array_sym.name = array_name.str();
    array_sym.type = array_type;
    array_sym.value = *zi;
    array_sym.location = array_loc;

    bool failed = symbol_table.add(array_sym);
    CHECK_RETURN(!failed);

    // Array start address
    index_exprt zero_idx{array_sym.symbol_expr(), from_integer(0, size_type())};
    address_of_exprt  array_start(zero_idx);

    // Linker-defined symbol_exprt pointing to start address
    symbolt start_sym;
    start_sym.is_static_lifetime = true;
    start_sym.is_lvalue = true;
    start_sym.is_state_var = true;
    start_sym.name = d["start-symbol"].value;
    start_sym.type = pointer_type(char_type());
    start_sym.value = array_start;
    linker_values.emplace(
      d["start-symbol"].value,
      std::make_pair(start_sym.symbol_expr(), array_start));

    // Since the value of the pointer will be a random CBMC address, write a
    // note about the real address in the object file
    auto it = std::find_if(
      to_json_array(data["addresses"]).begin(),
      to_json_array(data["addresses"]).end(),
      [&d](const jsont &add) {
        return add["sym"].value == d["start-symbol"].value;
      });
    if(it == to_json_array(data["addresses"]).end())
    {
      log.error() << "Start: Could not find address corresponding to symbol '"
                  << d["start-symbol"].value << "' (start of section)"
                  << messaget::eom;
      return 1;
    }
    source_locationt  start_loc;
    start_loc.set_file(linker_script);
    std::ostringstream start_comment;
    start_comment << "Pointer to beginning of object section '"
                  << d["section"].value << "'. Original address in object file"
                  << " is " << (*it)["val"].value;
    start_loc.set_comment(start_comment.str());
    start_sym.location = start_loc;

    auto start_sym_entry = symbol_table.insert(start_sym);
    if(!start_sym_entry.second)
      start_sym_entry.first = start_sym;

    if(has_end) // Same for pointer to end of array
    {
      plus_exprt array_end(array_start, array_size_expr);

      symbolt end_sym;
      end_sym.is_static_lifetime = true;
      end_sym.is_lvalue = true;
      end_sym.is_state_var = true;
      end_sym.name = d["end-symbol"].value;
      end_sym.type = pointer_type(char_type());
      end_sym.value = array_end;
      linker_values.emplace(
        d["end-symbol"].value,
        std::make_pair(end_sym.symbol_expr(), array_end));

      auto entry = std::find_if(
        to_json_array(data["addresses"]).begin(),
        to_json_array(data["addresses"]).end(),
        [&d](const jsont &add) {
          return add["sym"].value == d["end-symbol"].value;
        });
      if(entry == to_json_array(data["addresses"]).end())
      {
        log.debug() << "Could not find address corresponding to symbol '"
                    << d["end-symbol"].value << "' (end of section)"
                    << messaget::eom;
        return 1;
      }
      source_locationt  end_loc;
      end_loc.set_file(linker_script);
      std::ostringstream end_comment;
      end_comment << "Pointer to end of object section '" << d["section"].value
                  << "'. Original address in object file"
                  << " is " << (*entry)["val"].value;
      end_loc.set_comment(end_comment.str());
      end_sym.location = end_loc;

      auto end_sym_entry = symbol_table.insert(end_sym);
      if(!end_sym_entry.second)
        end_sym_entry.first = end_sym;
    }
  }

  // We've added every linker-defined symbol that marks the start or end of a
  // region. But there might be other linker-defined symbols with some random
  // address. These will have been declared extern too, so we need to give them
  // a value also. Here, we give them the actual value that they have in the
  // object file, since we're not assigning any object to them.
  for(const auto &d : to_json_array(data["addresses"]))
  {
    auto it=linker_values.find(irep_idt(d["sym"].value));
    if(it!=linker_values.end())
      // sym marks the start or end of a region; already dealt with.
      continue;

    // Perhaps this is a size symbol for a section whose size we truncated
    // earlier.
    irep_idt symbol_value;
    const auto &pair=truncated_symbols.find(d["sym"].value);
    if(pair==truncated_symbols.end())
      symbol_value=d["val"].value;
    else
    {
      log.debug()
        << "Truncating the value of symbol " << d["sym"].value << " from "
        << d["val"].value << " to " << MAX_FLATTENED_ARRAY_SIZE
        << " because it corresponds to the size of a too-large section."
        << messaget::eom;
      symbol_value=std::to_string(MAX_FLATTENED_ARRAY_SIZE);
    }

    source_locationt loc;
    loc.set_file(linker_script);
    loc.set_comment("linker script-defined symbol: char *"+
        d["sym"].value+"="+"(char *)"+id2string(symbol_value)+"u;");

    constant_exprt rhs(
      integer2bvrep(
        string2integer(id2string(symbol_value)),
        unsigned_int_type().get_width()),
      unsigned_int_type());

    typecast_exprt rhs_tc(rhs, pointer_type(char_type()));

    symbolt &symbol = symbol_table.get_writeable_ref(d["sym"].value);
    symbol.is_extern = false;
    symbol.is_static_lifetime = true;
    symbol.location = loc;
    symbol.type = pointer_type(char_type());
    symbol.value = rhs_tc;

    linker_values.emplace(
      irep_idt(d["sym"].value), std::make_pair(symbol.symbol_expr(), rhs_tc));
  }
  return 0;
}
#else
{
  goto_programt::instructionst initialize_instructions=gp.instructions;
  for(const auto &d : to_json_array(data["regions"]))
  {
    unsigned start=safe_string2unsigned(d["start"].value);
    unsigned size=safe_string2unsigned(d["size"].value);
    constant_exprt first=from_integer(start, size_type());
    constant_exprt second=from_integer(size, size_type());
    const code_typet void_t({}, empty_typet());
    code_function_callt f(
      symbol_exprt(CPROVER_PREFIX "allocated_memory", void_t), {first, second});

    source_locationt loc;
    loc.set_file(linker_script);
    loc.set_comment("linker script-defined region:\n"+d["commt"].value+":\n"+
        d["annot"].value);
    f.add_source_location()=loc;

    goto_programt::instructiont i;
    i.make_function_call(f);
    initialize_instructions.push_front(i);
  }

  if(!symbol_table.has_symbol(CPROVER_PREFIX "allocated_memory"))
  {
    symbolt sym;
    sym.name=CPROVER_PREFIX "allocated_memory";
    sym.pretty_name=CPROVER_PREFIX "allocated_memory";
    sym.is_lvalue=sym.is_static_lifetime=true;
    const code_typet void_t({}, empty_typet());
    sym.type=void_t;
    symbol_table.add(sym);
  }

  for(const auto &d : to_json_array(data["addresses"]))
  {
    source_locationt loc;
    loc.set_file(linker_script);
    loc.set_comment("linker script-defined symbol: char *"+
        d["sym"].value+"="+"(char *)"+d["val"].value+"u;");

    symbol_exprt lhs(d["sym"].value, pointer_type(char_type()));

    constant_exprt rhs;
    rhs.set_value(integer2bvrep(
      string2integer(d["val"].value), unsigned_int_type().get_width()));
    rhs.type()=unsigned_int_type();

    exprt rhs_tc =
      typecast_exprt::conditional_cast(rhs, pointer_type(char_type()));

    linker_values.emplace(
      irep_idt(d["sym"].value), std::make_pair(lhs, rhs_tc));

    code_assignt assign(lhs, rhs_tc);
    assign.add_source_location()=loc;
    goto_programt::instructiont assign_i;
    assign_i.make_assignment(assign);
    initialize_instructions.push_front(assign_i);
  }
  return 0;
}
#endif

int linker_script_merget::get_linker_script_data(
    std::list<irep_idt> &linker_defined_symbols,
    const symbol_tablet &symbol_table,
    const std::string &out_file,
    const std::string &def_out_file)
{
  for(auto const &pair : symbol_table.symbols)
  {
    if(
      pair.second.is_extern && pair.second.value.is_nil() &&
      pair.second.name != CPROVER_PREFIX "memory")
    {
      linker_defined_symbols.push_back(pair.second.name);
    }
  }

  std::ostringstream linker_def_str;
  std::copy(
    linker_defined_symbols.begin(),
    linker_defined_symbols.end(),
    std::ostream_iterator<irep_idt>(linker_def_str, "\n"));
  log.debug() << "Linker-defined symbols: [" << linker_def_str.str() << "]\n"
              << messaget::eom;

  temporary_filet linker_def_infile("goto-cc-linker-defs", "");
  std::ofstream linker_def_file(linker_def_infile());
  linker_def_file << linker_def_str.str();
  linker_def_file.close();

  std::vector<std::string> argv=
  {
    "ls_parse.py",
    "--script",   cmdline.get_value('T'),
    "--object",   out_file,
    "--sym-file", linker_def_infile(),
    "--out-file", def_out_file
  };

  if(log.get_message_handler().get_verbosity() >= messaget::M_DEBUG)
    argv.push_back("--very-verbose");
  else if(log.get_message_handler().get_verbosity() > messaget::M_RESULT)
    argv.push_back("--verbose");

  log.debug() << "RUN:";
  for(std::size_t i=0; i<argv.size(); i++)
    log.debug() << " " << argv[i];
  log.debug() << messaget::eom;

  int rc = run(argv[0], argv, linker_def_infile(), def_out_file, "");
  if(rc!=0)
    log.warning() << "Problem parsing linker script" << messaget::eom;

  return rc;
}

int linker_script_merget::goto_and_object_mismatch(
    const std::list<irep_idt> &linker_defined_symbols,
    const linker_valuest &linker_values)
{
  int fail=0;
  for(const auto &sym : linker_defined_symbols)
    if(linker_values.find(sym)==linker_values.end())
    {
      fail=1;
      log.error() << "Variable '" << sym
                  << "' was declared extern but never given "
                  << "a value, even in a linker script" << messaget::eom;
    }

  for(const auto &pair : linker_values)
  {
    auto it=std::find(linker_defined_symbols.begin(),
                      linker_defined_symbols.end(), pair.first);
    if(it==linker_defined_symbols.end())
    {
      fail=1;
      log.error()
        << "Linker script-defined symbol '" << pair.first << "' was "
        << "either defined in the C source code, not declared extern in "
        << "the C source code, or does not appear in the C source code"
        << messaget::eom;
    }
  }
  return fail;
}

int linker_script_merget::linker_data_is_malformed(const jsont &data) const
{
  if(!data.is_object())
    return true;

  const json_objectt &data_object = to_json_object(data);
  return (
    !(data_object.find("regions") != data_object.end() &&
      data_object.find("addresses") != data_object.end() &&
      data["regions"].is_array() && data["addresses"].is_array() &&
      std::all_of(
        to_json_array(data["addresses"]).begin(),
        to_json_array(data["addresses"]).end(),
        [](const jsont &j) {
          if(!j.is_object())
            return false;

          const json_objectt &address = to_json_object(j);
          return address.find("val") != address.end() &&
                 address.find("sym") != address.end() &&
                 address["val"].is_number() && address["sym"].is_string();
        }) &&
      std::all_of(
        to_json_array(data["regions"]).begin(),
        to_json_array(data["regions"]).end(),
        [](const jsont &j) {
          if(!j.is_object())
            return false;

          const json_objectt &region = to_json_object(j);
          return region.find("start") != region.end() &&
                 region.find("size") != region.end() &&
                 region.find("annot") != region.end() &&
                 region.find("commt") != region.end() &&
                 region.find("start-symbol") != region.end() &&
                 region.find("has-end-symbol") != region.end() &&
                 region.find("section") != region.end() &&
                 region["start"].is_number() && region["size"].is_number() &&
                 region["annot"].is_string() &&
                 region["start-symbol"].is_string() &&
                 region["section"].is_string() && region["commt"].is_string() &&
                 ((region["has-end-symbol"].is_true() &&
                   region.find("end-symbol") != region.end() &&
                   region["end-symbol"].is_string()) ||
                  (region["has-end-symbol"].is_false() &&
                   region.find("size-symbol") != region.end() &&
                   region.find("end-symbol") == region.end() &&
                   region["size-symbol"].is_string()));
        })));
}
