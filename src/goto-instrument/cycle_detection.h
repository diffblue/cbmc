/*******************************************************************\

Module: Cycle detection

Author: Vincent Nimal

Date: December 2011

\*******************************************************************/


#include <hash_cont.h>
#include <std_expr.h>
#include <std_code.h>
#include <expr_util.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include <fstream>
#include "rw_set.h"

// USING TOY C CODE
// an ugly mix of C and C++
#ifndef SUBCYCLES
#define SUBCYCLES
//#include "subcycles.h"
#endif

typedef enum {TSO, RMO, PSO, Power} modelt;

class event_grapht
{
  public:
    // from goto-program variable to location instrumented in cycle
    std::multimap<irep_idt,locationt> id_to_loc; 

    // from goto-program variable to location in the cycle
    std::multimap<irep_idt,locationt> id_to_cyc_loc;

    // variables to instrument
    std::set<irep_idt> var_to_instr;

    // constructor
    event_grapht();

    // destructor
    ~event_grapht();

    // converts goto-program var into cycle detector character
    const char add_var(const irep_idt id);

    // converts prog into event graph
    void convert_prg(value_setst &value_sets, 
      contextt &context, goto_functionst &goto_functions, modelt model);

    // collects cycles for TSO/PSO/RMO/Power in the graph
    void collect_cycles_tso(bool one_partition);
    void collect_cycles_pso(bool one_partition);
    void collect_cycles_rmo(bool one_partition);
    void collect_cycles_power(bool one_partition);

    // extracts pairs to instrument in TSO/PSO/RMO/Power cycles
    void to_instrument_tso();
    void to_instrument_pso();
    void to_instrument_rmo();
    void to_instrument_power();

    // strategies for pairs to instrument in each cycle
    void instrument_one_event_per_cycle();
    void instrument_one_read_per_cycle();
    void instrument_one_write_per_cycle();
    void instrument_all();
    void instrument_minimum_interference();
    void instrument_my_events(const std::set<int>);

    // from goto-program variable to cycle detector character, and converse
    typedef std::map<irep_idt,char> map_idt;
    typedef std::map<char,irep_idt> map_inv_idt;
    map_idt var_to_char;
    map_inv_idt char_to_var;

    typedef std::map<int,unsigned> map_vid_loct;
    map_vid_loct v_id_to_loc;

    // id, location_number (0 for local)
    typedef std::pair<irep_idt, int> aliast;
    typedef std::set<aliast> alias_classt;

    class aliasest {
      public:
        std::set<alias_classt> aliases;   

        void dependence_analysis(const aliast read_p, const aliast write_p);
        void copy_class(alias_classt&, const alias_classt&);
        bool dp(const vertex, const vertex, const map_inv_idt, const map_vid_loct);
        void dp_merge();
        void print();
    };

    // aliases per thread
    std::map<int,aliasest> map_aliases;

  protected:
    // whole graph of events
    list graph;
    // list of po events
    list poList;
    // list of po and rfe events
    list poUrfeList;
    // final list of cycles
    std::set<list> cycleList;

    std::ofstream file;
    std::ofstream output;
    std::ofstream ref;

    char char_var;
    unsigned unique_id;

    // cycle pairs storing
    typedef struct _instr_pairt {
      unsigned scycle;
      irep_idt svar;
      vertex svertex;
      bool stwo;
      irep_idt svar2;
      vertex svertex2;
    }* instr_pairt;

    typedef std::set<instr_pairt> pair_dbt;
    pair_dbt cycle_db;

    // instrumentation
    void po_reduction(const list);
    void to_instrument(const modelt);

    // internal mechanism
    bool not_local(const vertex);
    bool po_order(const vertex, const vertex);
    bool is_cycle(const list);
    bool thin_air(const list);
    bool select_pair(const vertex, list, std::ofstream &, modelt, unsigned, std::set<irep_idt> &);

    // graphic
    void remove_useless(list);
    void open_print_cycle();
    void print_cycle(list, unsigned, unsigned color, modelt model);
    void instr_print_cycle(const vertex);
    void close_print_cycle();  
    std::string order_qualify(const vertex prev,const vertex curr,const vertex succ, modelt model);
};



/* // Clean C++ code
class event_edget:public goto_programt::instructiont;

class cyclet: public std::stack<event_edget>;

typedef std::stack<cyclet> cycle_stackt;

class event_edget:public goto_programt::instructiont
{
public:
  event_edget():
    mark(_mark)
  {
  }

  // already visited?
  bool mark;

  // po transition
  event_edget next_by_po;

  // cmp transitions
  typedef std::list<event_edget> cmp_listt;
  cmp_listt cmps;

  void make_transitions(goto_programt goto_program);

  cycle_stackt cycle_detection();
  
protected:
  contextt &context;
};

class cyclet:public std::stack<event_edget>
{
public:
  cyclet()
  {
  }

  bool pair_unicity();

  bool local_restriction();

  bool exists_one_po();

  bool cyclic();

  // if those four properties are checked, this cycle is violating
  // SC, but not relaxed memory models => to instrument
}

*/

