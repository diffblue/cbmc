#include <goto-programs/goto_functions.h>

#include <cegis/options/literals.h>
#include <cegis/util/symbol_table_adapter.h>

symbol_table_adaptert::symbol_table_adaptert(symbol_tablet &st) :
    st(st)
{
}

symbol_table_adaptert::~symbol_table_adaptert()
{
}

namespace {
const char CPROVER_INITIALIZE[]="__CPROVER_initialize";
}
void symbol_table_adaptert::add_global_constant(const irep_idt &name,
    const typet &type, const source_locationt &loc) const
{
  symbolt new_symbol;
  new_symbol.name=name;
  new_symbol.type=type;
  new_symbol.base_name=new_symbol.name;
  new_symbol.location=loc;
  new_symbol.mode=ID_C;
  new_symbol.module=SYNTHESIS_MODULE;
  new_symbol.is_thread_local=false;
  new_symbol.is_static_lifetime=true;
  new_symbol.is_file_local=false;
  new_symbol.is_lvalue=true;
  st.add(new_symbol);
}

void symbol_table_adaptert::add_global_constant(const irep_idt &name,
    const exprt &value, goto_functionst &gf, const source_locationt &loc) const
{
  add_global_constant(name, value.type(), loc);
  symbolt &new_symbol=st.lookup(name);
  new_symbol.value=value;
  goto_programt &init_body=gf.function_map[CPROVER_INITIALIZE].body;
  const goto_programt::targett first=init_body.instructions.begin();
  const goto_programt::targett init=init_body.insert_after(first);
  init->type=ASSIGN;
  init->source_location=loc;
  init->code=code_assignt(new_symbol.symbol_expr(), value);
}
