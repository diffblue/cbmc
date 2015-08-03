#include <algorithm>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/std_types.h>
#include <util/arith_tools.h>
#include <ansi-c/c_types.h>
#include <goto-programs/goto_functions.h>
#include <cegis/options/cegis_options.h>
#include <cegis/options/literals.h>
#include <cegis/util/source_location_factory.h>
#include <cegis/util/goto_program_adapter.h>
#include <cegis/symex/variables_factory.h>
#include <cegis/symex/target_program_factory.h>

target_program_factoryt::target_program_factoryt(symbol_tablet &symbol_table,
    goto_functionst &goto_functions, const cegis_optionst &options,
    source_location_factoryt &lfactory) :
    symbol_table(symbol_table), gf(goto_functions), options(options), lfactory(
        lfactory)
{
}

target_program_factoryt::~target_program_factoryt()
{
}

namespace {
std::string concat(std::string lhs, const irep_idt &rhs)
{
  return lhs+=id2string(rhs);
}

const char SYNTHESIS_PROG_SIZE[]="__CPROVER_synthesis_program_size_";

void limit_prog_size(const cegis_optionst &options, goto_programt &body,
    const exprt &prog_size_symbol, const source_locationt &loc)
{
  const unsigned int max_prog_size=options.max_prog_size();
  const constant_exprt rhs=from_integer(max_prog_size, unsigned_int_type());
  const goto_programt::targett assume_prog_size=body.add_instruction(ASSUME);
  const binary_predicate_exprt cond(prog_size_symbol, ID_le, rhs);
  assume_prog_size->guard=cond;
  assume_prog_size->source_location=loc;
}

symbol_typet get_instr_type()
{
  return symbol_typet(SYNTHESIS_INSTR_TYPE_SYMBOL_NAME);
}

const char SIZE_PARAM[]="__CPROVER_synthesis_execute_prog_size";
const char PROG_PARAM[]="__CPROVER_synthesis_execute_prog";

void add_function_body(const symbol_tablet &st, goto_functionst &gf,
    const std::string &fn, const code_declt &szdecl,
    const code_declt &prog_decl, source_location_factoryt &lfactory)
{
  goto_functionst::function_mapt &fm=gf.function_map;
  const goto_functionst::function_mapt::iterator entry=fm.find(fn);
  assert(fm.end() != entry);
  entry->second.body_available=true;
  goto_programt &body=entry->second.body;
  const exprt &prog_size=szdecl.symbol();
  const exprt &prog=prog_decl.symbol();
  code_function_callt call;
  const symbolt &exec_symbol=st.lookup(SYNTHESIS_EXECUTE);
  call.function()=exec_symbol.symbol_expr();
  // XXX: Function call paramerers have nondet values! Using global variables instead.
  /*//const constant_exprt prsz=from_integer(0, unsigned_int_type());
   //call.arguments().push_back(prsz);
   call.arguments().push_back(prog_size);
   const constant_exprt first_index(from_integer(0, size_type()));
   const index_exprt first(prog, first_index);
   const address_of_exprt prog_ref(first);
   call.arguments().push_back(prog_ref);*/
  const symbol_exprt size_param(st.lookup(SIZE_PARAM).symbol_expr());
  const goto_programt::targett assign_size=body.add_instruction(ASSIGN);
  assign_size->code=code_assignt(size_param, prog_size);
  assign_size->source_location=lfactory(fn);
  const symbol_exprt prog_param(st.lookup(PROG_PARAM).symbol_expr());
  const constant_exprt first_index(from_integer(0, size_type()));
  const index_exprt first(prog, first_index);
  const address_of_exprt array_ref(first);
  const goto_programt::targett assign_prog=body.add_instruction(ASSIGN);
  assign_prog->code=code_assignt(prog_param, array_ref);
  assign_prog->source_location=lfactory(fn);
  // XXX: Function call paramerers have nondet values! Using global variables instead.
  const goto_programt::targett call_exec=body.add_instruction(FUNCTION_CALL);
  call_exec->code=call;
  call_exec->source_location=lfactory(fn);
  body.add_instruction(END_FUNCTION)->source_location=lfactory(fn);
  // XXX: Add argument and return variables to __CPROVER_synthesis_vars?
}

class create_target_programt
{
  const cegis_optionst &options;
  symbol_tablet &st;
  goto_functionst &gf;
  source_location_factoryt &lfactory;
public:
  create_target_programt(const cegis_optionst &options,
      symbol_tablet &symbol_table, goto_functionst &goto_functions,
      source_location_factoryt &lfactory) :
      options(options), st(symbol_table), gf(goto_functions), lfactory(lfactory)
  {
  }

  ~create_target_programt()
  {
  }

  void operator()(const std::string &function_name) const
  {
    const std::string synthesis_entry(options.entry_function_name());
    goto_programt &body=get_program_body(gf, synthesis_entry);
    const goto_program_adaptert adapter(st, body);
    const std::string prog_size(concat(SYNTHESIS_PROG_SIZE, function_name));
    const std::string entry_name=options.entry_function_name();
    const source_locationt size_loc(lfactory(entry_name));
    const typet sztype(unsigned_int_type());
    code_declt &szdecl=adapter.append_decl(prog_size, sztype, size_loc);
    const exprt &size=szdecl.symbol();
    limit_prog_size(options, body, size, lfactory(entry_name));
    const std::string prog(concat(SYNTHESIS_PROG, function_name));
    const array_typet prog_type(get_instr_type(), size);
    const source_locationt prog_loc(lfactory(entry_name));
    code_declt &prog_decl=adapter.append_decl(prog, prog_type, prog_loc);
    add_function_body(st, gf, function_name, szdecl, prog_decl, lfactory);
  }
};
}

void target_program_factoryt::operator ()() const
{
  const std::list<std::string> functions=options.target_function_names();
  const create_target_programt create_prog(options, symbol_table, gf, lfactory);
  std::for_each(functions.begin(), functions.end(), create_prog);
}

void add_target_programs(class symbol_tablet &symbol_table,
    class goto_functionst &gf, const class cegis_optionst &options,
    class source_location_factoryt &lfactory)
{
  const target_program_factoryt tpf(symbol_table, gf, options, lfactory);
  tpf();
}
