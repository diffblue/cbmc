/*******************************************************************\

Module: Dump Goto-Program as C/C++ Source

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <list>

#include <analyses/natural_loops.h>

class goto_program2codet
{
  typedef std::list<irep_idt> id_listt;
  typedef hash_set_cont<irep_idt,irep_id_hash> id_sett;
  typedef std::map<goto_programt::const_targett, goto_programt::const_targett> loopt;
  typedef hash_map_cont<irep_idt, unsigned, irep_id_hash> dead_mapt;
  typedef std::list<std::pair<goto_programt::const_targett, bool> >
    loop_last_stackt;

  struct caset
  {
    const exprt value; // condition upon which this case is taken
    goto_programt::const_targett case_selector; // branching from ...
    goto_programt::const_targett case_start; // ... to
    goto_programt::const_targett case_last; // last instruction of case

    caset(const goto_programt &goto_program,
          const exprt &v,
          goto_programt::const_targett sel,
          goto_programt::const_targett st):
      value(v), case_selector(sel), case_start(st),
      case_last(goto_program.instructions.end())
    {
    }
  };
  typedef std::list<caset> cases_listt;

public:
  goto_program2codet(
      const irep_idt &identifier,
      const goto_programt &_goto_program,
      symbol_tablet &_symbol_table,
      code_blockt &_dest,
      id_listt &_local_static,
      id_listt &_type_names,
      std::set<std::string> &_system_headers):
    func_name(identifier),
    goto_program(_goto_program),
    symbol_table(_symbol_table),
    ns(_symbol_table),
    toplevel_block(_dest),
    local_static(_local_static),
    type_names(_type_names),
    system_headers(_system_headers)
  {
    assert(local_static.empty());

    for(id_listt::const_iterator
        it=type_names.begin();
        it!=type_names.end();
        ++it)
      type_names_set.insert(*it);
  }

  void operator()();

protected:
  const irep_idt &func_name;
  const goto_programt &goto_program;
  symbol_tablet &symbol_table;
  const namespacet ns;
  code_blockt &toplevel_block;
  id_listt &local_static;
  id_listt &type_names;
  std::set<std::string> &system_headers;
  hash_set_cont<exprt, irep_hash> va_list_expr;

  natural_loopst loops;
  loopt loop_map;
  id_sett labels_in_use;
  dead_mapt dead_map;
  loop_last_stackt loop_last_stack;
  id_sett local_static_set;
  id_sett type_names_set;
  id_sett const_removed;

  void build_loop_map();
  void build_dead_map();
  void scan_for_varargs();

  void cleanup_code(codet &code, const irep_idt parent_stmt);

  void cleanup_code_block(
    codet &code,
    const irep_idt parent_stmt);

  void cleanup_code_ifthenelse(
    codet &code,
    const irep_idt parent_stmt);

  void cleanup_expr(exprt &expr, bool no_typecast);

  void add_local_types(const typet &type);

  void remove_const(typet &type);

  goto_programt::const_targett convert_instruction(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);

  void convert_labels(
      goto_programt::const_targett target,
      codet &dest);

  goto_programt::const_targett convert_assign(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);

  goto_programt::const_targett convert_assign_varargs(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);

  void convert_assign_rec(
      const code_assignt &assign,
      codet &dest);

  goto_programt::const_targett convert_return(
      goto_programt::const_targett target,
      codet &dest);

  goto_programt::const_targett convert_decl(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);

  goto_programt::const_targett convert_do_while(
      goto_programt::const_targett target,
      goto_programt::const_targett loop_end,
      codet &dest);

  goto_programt::const_targett convert_goto(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);

  goto_programt::const_targett convert_goto_while(
      goto_programt::const_targett target,
      goto_programt::const_targett loop_end,
      codet &dest);

  goto_programt::const_targett convert_goto_switch(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);

  goto_programt::const_targett convert_goto_if(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);

  goto_programt::const_targett convert_goto_break_continue(
      goto_programt::const_targett target,
      codet &dest);

  goto_programt::const_targett convert_goto_goto(
      goto_programt::const_targett target,
      codet &dest);

  goto_programt::const_targett convert_start_thread(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);

  goto_programt::const_targett convert_throw(
      goto_programt::const_targett target,
      codet &dest);

  goto_programt::const_targett convert_catch(
      goto_programt::const_targett target,
      goto_programt::const_targett upper_bound,
      codet &dest);
};

