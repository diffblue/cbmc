/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include <util/i2string.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/arith_tools.h>

#include <ansi-c/c_types.h>

#include <goto-programs/goto_program.h>

#include <cegis/options/literals.h>
#include <cegis/options/cegis_options.h>
#include <cegis/util/source_location_factory.h>
#include <cegis/util/goto_program_adapter.h>
#include <cegis/util/symbol_table_adapter.h>
#include <cegis/symex/variables_factory.h>

variables_factoryt::variables_factoryt(symbol_tablet &st,
    goto_functionst &goto_functions, const cegis_optionst &options,
    source_location_factoryt &source_location_factory) :
    st(st), gf(goto_functions), options(options), loc_fac(
        source_location_factory)
{
}

variables_factoryt::~variables_factoryt()
{
}

namespace {
void create_temp_variables(symbol_tablet &st, goto_functionst &gf,
    source_location_factoryt &lfac, const cegis_optionst &options)
{
  const symbol_table_adaptert adapter(st);
  const typet type(signed_int_type()); // XXX: Different/more types?
  const size_t num_funcs=options.total_target_functions();
  const size_t max_tmp_vars=options.max_prog_size() * num_funcs;
  const std::string entry_name=options.entry_function_name();
  goto_programt &entry=get_program_body(gf, entry_name);
  const goto_programt::targett first=entry.instructions.begin();
  for (size_t i=0; i < max_tmp_vars; ++i)
  {
    const source_locationt loc(lfac(SYNTHESIS_INIT));
    std::string name(CPROVER_SYNTHESIS_TMPVAR_PREFIX);
    name+=i2string(i);
    adapter.add_global_constant(name, type, loc);
    const symbol_exprt symbol(name, type);
    // Self-assign in order to trace nondet value
    const goto_programt::targett assign=entry.insert_after(first);
    assign->type=ASSIGN;
    assign->source_location=loc;
    assign->code=code_assignt(symbol, symbol);
  }
}

class containst: public std::unary_function<const char * const, bool>
{
  const std::string &str;
public:
  containst(const irep_idt &id) :
      str(id2string(id))
  {
  }
  bool operator()(const char * const needle) const
  {
    return std::string::npos != str.find(needle);
  }
};

bool is_meta_symbol(const irep_idt &symbol)
{
  const containst p(symbol);
  const std::unary_negate<containst> n(p);
  return p(CPROVER_VARIABLE_PREFIX) && n(CPROVER_SYNTHESIS_ARG_PREFIX)
      && n(CPROVER_SYNTHESIS_PRIVATE_ARG_PREFIX)
      && n(CPROVER_SYNTHESIS_CONST_PREFIX) && n(CPROVER_SYNTHESIS_TMPVAR_PREFIX)
      && n(CPROVER_SYNTHESIS_WRITEONLY_PREFIX)
      && n(CPROVER_SYNTHESIS_SKOLEM_PREFIX)
      && n(CPROVER_SYNTHESIS_RANKING_PREFIX);
}

bool is_return_value(const irep_idt &symbol)
{
  return containst(symbol)("#return_value");
}

bool is_readonly(const irep_idt &symbol)
{
  const containst p(symbol);
  return p(CPROVER_SYNTHESIS_ARG_PREFIX) || p(CPROVER_SYNTHESIS_CONST_PREFIX)
      || p(CPROVER_SYNTHESIS_TMPVAR_PREFIX) /* TODO: Not all tmps should be const */;
}

class categorise_varst
{
  exprt::operandst &wo;
  exprt::operandst &rw;
  exprt::operandst &ro;
  exprt::operandst &skolem;
  exprt::operandst &ranking;
public:
  categorise_varst(exprt::operandst &wo, exprt::operandst &rw,
      exprt::operandst &ro, exprt::operandst &skolem, exprt::operandst &ranking) :
      wo(wo), rw(rw), ro(ro), skolem(skolem), ranking(ranking)
  {
  }
  ~categorise_varst()
  {
  }
  void operator()(const std::pair<irep_idt, symbolt> &named_symbol)
  {
    const symbolt &symbol=named_symbol.second;
    if (symbol.is_type || !symbol.is_static_lifetime) return;
    const std::string &file=id2string(symbol.location.get_file());
    if (file.find(BUILTIN_MODULE) != std::string::npos) return;
    const irep_idt &symbol_name=symbol.name;
    if (is_meta_symbol(symbol_name)) return;
    if (is_return_value(symbol_name)) return;
    const containst c(symbol_name);
    if (c(CPROVER_SYNTHESIS_PRIVATE_ARG_PREFIX)) return;
    if (ID_code == symbol.type.id()) return;
    const address_of_exprt entry(symbol.symbol_expr());
    if (c(CPROVER_SYNTHESIS_WRITEONLY_PREFIX)) return wo.push_back(entry);
    if (c(CPROVER_SYNTHESIS_SKOLEM_PREFIX)) return skolem.push_back(entry);
    if (c(CPROVER_SYNTHESIS_RANKING_PREFIX)) return ranking.push_back(entry);
    if (is_readonly(symbol_name)) return ro.push_back(entry);
    rw.push_back(entry);
  }
};

const char VARS[]="__CPROVER_synthesis_vars";
const char NUM_VARS[]="__CPROVER_synthesis_num_vars";
const char WONLY[]="__CPROVER_synthesis_offset_writeonly";
const char RDONLY[]="__CPROVER_synthesis_offset_readonly";
const char SKOLEM[]="__CPROVER_synthesis_offset_skolem";
const char RANKING[]="__CPROVER_synthesis_offset_ranking";

void assign_offset(const symbol_tablet &st, goto_programt &body,
    const char * const name, const exprt &value, const source_locationt &loc)
{
  const goto_programt::targett assign=body.add_instruction(ASSIGN);
  const symbol_exprt lhs(st.lookup(name).symbol_expr());
  assign->code=code_assignt(lhs, value);
  assign->source_location=loc;
}
}

void variables_factoryt::operator ()() const
{
  create_temp_variables(st, gf, loc_fac, options);
  exprt::operandst wo_vars;
  exprt::operandst rw_vars;
  exprt::operandst ro_vars;
  exprt::operandst skolem;
  exprt::operandst ranking;
  const categorise_varst op(wo_vars, rw_vars, ro_vars, skolem, ranking);
  std::for_each(st.symbols.begin(), st.symbols.end(), op);
  const typet uintt(unsigned_int_type());
  const constant_exprt skolem_offset(from_integer(skolem.size(), uintt));
  skolem.insert(skolem.end(), ranking.begin(), ranking.end());
  const constant_exprt ranking_offset(from_integer(skolem.size(), uintt));
  skolem.insert(skolem.end(), wo_vars.begin(), wo_vars.end());
  const constant_exprt wo_offset(from_integer(skolem.size(), uintt));
  skolem.insert(skolem.end(), rw_vars.begin(), rw_vars.end());
  const constant_exprt ro_offset(from_integer(skolem.size(), uintt));
  skolem.insert(skolem.end(), ro_vars.begin(), ro_vars.end());
  const size_t num_vars=skolem.size();
  const constant_exprt size_expr(from_integer(num_vars, uintt));
  const std::string entry_func_name=options.entry_function_name();
  goto_programt &entry=get_program_body(gf, entry_func_name);
  const goto_program_adaptert adapter(st, entry);
  const goto_programt::targett assign_num=entry.add_instruction(ASSIGN);
  const symbol_exprt num_lhs(st.lookup(NUM_VARS).symbol_expr());
  assign_num->code=code_assignt(num_lhs, size_expr);
  assign_num->source_location=loc_fac(entry_func_name);
  assign_offset(st, entry, SKOLEM, skolem_offset, loc_fac(entry_func_name));
  assign_offset(st, entry, RANKING, ranking_offset, loc_fac(entry_func_name));
  assign_offset(st, entry, WONLY, wo_offset, loc_fac(entry_func_name));
  assign_offset(st, entry, RDONLY, ro_offset, loc_fac(entry_func_name));
  const symbol_exprt vars(st.lookup(VARS).symbol_expr());
  for (unsigned int i=0; i < num_vars; ++i)
  {
    const constant_exprt index(from_integer(i, size_type()));
    const index_exprt lhs(vars, index);
    const goto_programt::targett assign_var=entry.add_instruction(ASSIGN);
    assign_var->code=code_assignt(lhs, skolem.at(i));
    assign_var->source_location=loc_fac(entry_func_name);
  }
}

void create_symex_learning_variables(symbol_tablet &st, goto_functionst &gf,
    const cegis_optionst &options, source_location_factoryt &loc_fac)
{
  const variables_factoryt f(st, gf, options, loc_fac);
  f();
}
