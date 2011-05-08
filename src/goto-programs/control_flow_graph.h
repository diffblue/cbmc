/*
 * control_flow_graph.h
 *
 *  Created on: August 18, 2010
 *      Author: Alastair Donaldson
 */

#ifndef CONTROL_FLOW_GRAPH_H_
#define CONTROL_FLOW_GRAPH_H_

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program.h>

#include <util/std_expr.h>

#define forall_cfg_nodes(it, cfg) \
  for(CFGt::nodes_sett::const_iterator it = (cfg).begin(); \
      it != (cfg).end(); it++)

/* Control Flow Graphs */

class CFG_nodet
{
public:

        virtual ~CFG_nodet()
        {
        }

	/* code, function, location and type determine the instruction represented by the CFG node */
	codet code;
	irep_idt function;
	locationt location;
	goto_program_instruction_typet type;

	exprt reasoning_guard; /* Used if instruction is assert/assume, otherwise meaningless */
	exprt jump_condition; /* Used if successor_jump is not NULL.  In this case, if jump_condition is true then the successor is successor_jump */
	CFG_nodet* successor_next; /* Default successor, or successor if jump_condition is false */
	CFG_nodet* successor_jump; /* Successor if jump condition is true */

	std::set<CFG_nodet*> predecessors; /* Nodes that point to this node via successor_next or successor_jump fields.  Set when parent CFG is updated */
	int id; /* Id for node, which is set when the parent CFG is updated */

	CFG_nodet(goto_programt::instructiont& goto_program_instruction);

	CFG_nodet(codet code, irep_idt function, locationt location, goto_program_instruction_typet type)
		: code(code), function(function), location(location), type(type)
	{
		reasoning_guard = false_exprt();
		jump_condition = false_exprt();
		successor_next = NULL;
		successor_jump = NULL;
	}

	virtual void output_special_info(std::ostream&) const;

	bool operator == (const CFG_nodet& other) const;

};

class dominator_infot;

class loop_infot;

class CFGt
{

public:

	typedef std::list<CFG_nodet*> nodest;
	typedef std::list<const CFG_nodet*> const_nodest;

	typedef std::set<CFG_nodet*> nodes_sett;
	typedef std::set<const CFG_nodet*> nodes_const_sett;
	typedef std::map<const CFG_nodet*, CFG_nodet*> nodes_mappingt;

	typedef std::vector<CFG_nodet*> nodes_vectort;
	typedef std::vector<const CFG_nodet*> const_nodes_vectort;

	contextt& context;

private:
	CFG_nodet* entry_node;
	CFG_nodet* last_node_added;
	nodes_sett nodes;
	const_nodes_vectort ordered_nodes;

public:

	CFGt(const CFGt& other);

	CFGt(contextt& context) : context(context)
	{
		nodes.clear();
		entry_node = NULL;
		last_node_added = NULL;
	}

	virtual ~CFGt();

	void initialize(goto_programt& program);

	const const_nodes_vectort& get_ordered_nodes() const;

	nodes_sett::const_iterator begin() const;

	nodes_sett::const_iterator end() const;

	void output(std::ostream& out, bool show_predecessors=false) const;

	void output_node(const CFG_nodet& node,	std::ostream& out, bool show_predecessors = false) const;

	void to_goto_program(
      goto_programt& program, 
      std::map<goto_programt::const_targett, std::pair<unsigned int, unsigned int> >* loop_header_instruction_points = NULL,
      std::map<const CFG_nodet*, goto_programt::const_targett>* node_to_target = NULL) const;

	virtual CFG_nodet& append_node(CFG_nodet node);

	virtual CFG_nodet& add_node(CFG_nodet node);

	void patchup_pointers(std::map<const CFG_nodet*, CFG_nodet*>& patchup_map);

	// Transformations may lead to CFG nodes with a non-trivial jump condition, but only one
	// successor.  This method changes such nodes to 'assume's
	void fix_jumps();

	void update();

	void transform_to_monolithic_loop();

	// Re-arranges CFG so that all declarations appear at start
	void hoist_declarations();


	const CFG_nodet& get_initial() const;

	CFG_nodet& get_initial();

	unsigned int size() const;

	bool contains(const CFG_nodet& n) const;

	const CFG_nodet& get_last_added_node() const;

	CFG_nodet& get_last_added_node();

	void order_nodes_raw(); // Should only be called for debugging purposes

	void unwind_loop(const CFG_nodet* header, const loop_infot& loop_info, unsigned int unwind_count);

  //instrument the control flow graph with assume or assert statements
  void instrument_with_guards(
    const std::map<const CFG_nodet*, exprt>& instruction_to_invariant, 
    bool assert);

private:
	void add_returns();
	void remove_self_loops();
	void calculate_prececessors();
	void collect_garbage();
	void sanity_check() const;
	bool all_non_back_edge_predecessors_ordered(
			const CFG_nodet* dest,
			const const_nodes_vectort& ordered,
			const dominator_infot& dominator_info) const;
	void order_nodes();

protected:
	CFG_nodet& append_node_ptr(CFG_nodet* node);
	CFG_nodet& add_node_ptr(CFG_nodet* node);

	virtual void check_cfg_point(goto_programt::const_targett inst, const CFG_nodet* node, std::map<goto_programt::const_targett, std::pair<unsigned int, unsigned int> >* loop_header_instruction_points) const;


};


/* Some utility functions */

void patchup_pointers_in_nodes(CFGt::nodest& nodes, std::map<const CFG_nodet*, CFG_nodet*>& patchup_map);

void patchup_pointers_in_nodes(CFGt::nodes_sett& nodes, std::map<const CFG_nodet*, CFG_nodet*>& patchup_map);

goto_programt& find_main(goto_functionst& goto_functions, contextt& context);

goto_programt& find_enclosing_main(goto_functionst& goto_functions, contextt& context);

void redirect_pointer(CFG_nodet*& pointer_to_redirect, CFGt::nodes_mappingt& original_to_cloned);

#endif
