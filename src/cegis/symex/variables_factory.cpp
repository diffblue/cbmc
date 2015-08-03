#include <algorithm>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/arith_tools.h>
#include <ansi-c/c_types.h>
#include <goto-programs/goto_program.h>
#include <cegis/options/literals.h>
#include <cegis/options/cegis_options.h>
#include <cegis/util/source_location_factory.h>
#include <cegis/util/goto_program_adapter.h>
#include <cegis/symex/variables_factory.h>

variables_factoryt::variables_factoryt(symbol_tablet &symbol_table,
    goto_functionst &goto_functions, const cegis_optionst &options,
    source_location_factoryt &source_location_factory) :
    symbol_table(symbol_table), gf(goto_functions), options(options), loc_fac(
        source_location_factory)
{
}

variables_factoryt::~variables_factoryt()
{
}

namespace {
bool is_non_synthesis_cprover_symbol(const irep_idt &symbol)
{
  const std::string &name=id2string(symbol);
  if (std::string::npos == name.find(CPROVER_VARIABLE_PREFIX)) return false;
  return std::string::npos == name.find(CPROVER_SYNTHESIS_VARIABLE_PREFIX);
}

bool is_return_value(const irep_idt &symbol)
{
  return std::string::npos != id2string(symbol).find("#return_value");
}

bool is_readonly(const irep_idt &symbol)
{
  const std::string &name(id2string(symbol));
  return std::string::npos != name.find(CPROVER_SYNTHESIS_VARIABLE_PREFIX);
}

class create_synthesis_vars_initialisert
{
  exprt::operandst &writeable;
  exprt::operandst &readonly;
public:
  create_synthesis_vars_initialisert(exprt::operandst &writeable,
      exprt::operandst &readonly) :
      writeable(writeable), readonly(readonly)
  {
  }
  ~create_synthesis_vars_initialisert()
  {
  }
  void operator()(const std::pair<irep_idt, symbolt> &named_symbol)
  {
    const symbolt &symbol=named_symbol.second;
    if (symbol.is_type || !symbol.is_static_lifetime) return;
    const std::string &file=id2string(symbol.location.get_file());
    if (file.find(BUILTIN_MODULE) != std::string::npos) return;
    const irep_idt &symbol_name=symbol.name;
    if (is_non_synthesis_cprover_symbol(symbol_name)) return;
    if (is_return_value(symbol_name)) return;
    if (ID_code == symbol.type.id()) return;
    const address_of_exprt entry(symbol.symbol_expr());
    if (is_readonly(symbol_name)) readonly.push_back(entry);
    else writeable.push_back(entry);
  }
};

const char VARS[]="__CPROVER_synthesis_vars";
const char NUM_VARS[]="__CPROVER_synthesis_num_vars";
const char RDONLY[]="__CPROVER_synthesis_readonly_offset";
}

void variables_factoryt::operator ()() const
{
  // TODO: Create temporary variables
  exprt::operandst variables;
  exprt::operandst rdonly_vars;
  const create_synthesis_vars_initialisert op(variables, rdonly_vars);
  std::for_each(symbol_table.symbols.begin(), symbol_table.symbols.end(), op);
  const typet uintt(unsigned_int_type());
  const constant_exprt readonly_offset(from_integer(variables.size(), uintt));
  variables.insert(variables.end(), rdonly_vars.begin(), rdonly_vars.end());
  const size_t num_vars=variables.size();
  const constant_exprt size_expr(from_integer(num_vars, uintt));
  const std::string entry_func_name=options.entry_function_name();
  goto_programt &entry=get_program_body(gf, entry_func_name);
  const goto_program_adaptert adapter(symbol_table, entry);
  const goto_programt::targett assign_num=entry.add_instruction(ASSIGN);
  const symbol_exprt num_lhs(symbol_table.lookup(NUM_VARS).symbol_expr());
  assign_num->code=code_assignt(num_lhs, size_expr);
  assign_num->source_location=loc_fac(entry_func_name);
  const goto_programt::targett assign_readonly=entry.add_instruction(ASSIGN);
  const symbol_exprt rdonly_lhs(symbol_table.lookup(RDONLY).symbol_expr());
  assign_readonly->code=code_assignt(rdonly_lhs, readonly_offset);
  assign_readonly->source_location=loc_fac(entry_func_name);
  const symbol_exprt vars(symbol_table.lookup(VARS).symbol_expr());
  for (unsigned int i=0; i < num_vars; ++i)
  {
    const constant_exprt index(from_integer(i, size_type()));
    const index_exprt lhs(vars, index);
    const goto_programt::targett assign_var=entry.add_instruction(ASSIGN);
    assign_var->code=code_assignt(lhs, variables.at(i));
    assign_var->source_location=loc_fac(entry_func_name);
  }
}

void create_symex_learning_variables(symbol_tablet &st, goto_functionst &gf,
    const cegis_optionst &options, source_location_factoryt &loc_fac)
{
  const variables_factoryt f(st, gf, options, loc_fac);
  f();
}
