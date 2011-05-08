/*
 * control_flow_graph.cpp
 *
 *  Created on: August 18, 2010
 *      Author: Alastair Donaldson
 */

#include <ansi-c/c_types.h>
#include <util/expr_util.h>
#include <util/arith_tools.h>
#include <util/config.h>
#include <util/std_code.h>



#include "control_flow_graph.h"
#include "dominator_info.h"
#include "loops.h"

/* Control flow graphs */

static void output_single_node(const CFG_nodet& node,
			std::ostream& out, const namespacet& ns, const CFGt::const_nodes_vectort* ordering, bool show_predecessors);


void redirect_pointer(CFG_nodet*& pointer_to_redirect, CFGt::nodes_mappingt& original_to_cloned)
{
	if(NULL != pointer_to_redirect)
	{
		if(original_to_cloned.find(pointer_to_redirect) != original_to_cloned.end())
		{
			pointer_to_redirect = original_to_cloned[pointer_to_redirect];
		}
	}

}

void patchup_pointers_in_nodes(CFGt::nodest& nodes, std::map<const CFG_nodet*, CFG_nodet*>& patchup_map)
{
	for(CFGt::nodest::iterator
			it = nodes.begin();
			it != nodes.end();
			it++)
	{
		redirect_pointer((*it)->successor_next, patchup_map);
		redirect_pointer((*it)->successor_jump, patchup_map);
	}
}

void patchup_pointers_in_nodes(CFGt::nodes_sett& nodes, std::map<const CFG_nodet*, CFG_nodet*>& patchup_map)
{
	for(CFGt::nodes_sett::iterator
			it = nodes.begin();
			it != nodes.end();
			it++)
	{
		redirect_pointer((*it)->successor_next, patchup_map);
		redirect_pointer((*it)->successor_jump, patchup_map);
	}
}


CFGt::CFGt(const CFGt& other) : context(other.context)
{
	nodes.clear();
	entry_node = NULL;
	last_node_added = NULL;

	nodes_mappingt patchup_map;

	for(nodes_sett::const_iterator it = other.nodes.begin(); it != other.nodes.end(); it++)
	{
		CFG_nodet* new_node = new CFG_nodet(**it);
		patchup_map[*it] = new_node;
		nodes.insert(new_node);
		if(other.entry_node == *it)
		{
			assert(NULL == entry_node);
			entry_node = new_node;
		}
		if(other.last_node_added == *it)
		{
			assert(NULL == last_node_added);
			last_node_added = new_node;
		}
	}

	patchup_pointers(patchup_map);
	update();

}


void CFGt::patchup_pointers(std::map<const CFG_nodet*, CFG_nodet*>& patchup_map)
{
	patchup_pointers_in_nodes(nodes, patchup_map);
}


void CFGt::fix_jumps()
{
	nodes_mappingt patchup_map;
	for(CFGt::nodes_sett::iterator it = nodes.begin(); it != nodes.end(); it++)
	{
		if((GOTO == (*it)->type) && ((*it)->jump_condition != true_exprt()))
		{
			if(NULL == (*it)->successor_next)
			{
				assert(NULL != (*it)->successor_jump);
				CFG_nodet new_node(code_assumet(), (*it)->function, (*it)->location, ASSUME);
				new_node.reasoning_guard = (*it)->jump_condition;
				new_node.successor_next = (*it)->successor_jump;
				CFG_nodet& added_node = add_node(new_node);
				patchup_map[*it] = &added_node;
			} else if(NULL == (*it)->successor_jump) {
				assert(NULL != (*it)->successor_next);
				CFG_nodet new_node(code_assumet(), (*it)->function, (*it)->location, ASSUME);
				new_node.reasoning_guard = not_exprt((*it)->jump_condition);
				new_node.successor_next = (*it)->successor_next;
				CFG_nodet& added_node = add_node(new_node);
				patchup_map[*it] = &added_node;
			}
		}
	}
	patchup_pointers(patchup_map);
}

void CFG_nodet::output_special_info(std::ostream&) const
{
	return;
}

CFG_nodet::CFG_nodet(goto_programt::instructiont& goto_program_instruction)
{
	this->code = goto_program_instruction.code;
	this->function = goto_program_instruction.function;
	this->location = goto_program_instruction.location;
	this->type = goto_program_instruction.type;

	if(this->type == ASSERT || this->type == ASSUME) {
		this->reasoning_guard = goto_program_instruction.guard;
	} else {
		this->reasoning_guard = true_exprt();
	}

	if(this->type == GOTO) {
		contextt ctx;
		/* We only deal with deterministic gotos */
		assert(goto_program_instruction.targets.size() == 1);
		this->jump_condition = goto_program_instruction.guard;
	} else {
		this->jump_condition = false_exprt();
	}

	this->successor_next = NULL;
	this->successor_jump = NULL;
}


bool CFG_nodet::operator == (const CFG_nodet& other) const
{
	return code == other.code && function == other.function && location == other.location && type == other.type &&
			reasoning_guard == other.reasoning_guard && jump_condition == other.jump_condition &&
			successor_jump == other.successor_jump && successor_next == other.successor_next;
}


static goto_programt::targett get_following_instruction(goto_programt::targett current) {
	goto_programt::targett result = current;
	result++;
	return result;
}

void CFGt::initialize(goto_programt& program) {

	assert(nodes.empty());
	assert(NULL == entry_node);
	assert(NULL == last_node_added);

	namespacet ns(context);

	/* First, for every instruction in the function,
	 * add a node to the CFG.  Keep a mapping from instructions
	 * to nodes, so that later we can add edges to the CFG
	 */
	std::map<goto_programt::targett, CFG_nodet*> instructions_to_nodes;
	for(goto_programt::targett
			it = program.instructions.begin();
			it != program.instructions.end();
			it++)
	{
		if(it->type == END_FUNCTION)
		{
			CFG_nodet return_node(code_returnt(), it->function, it->location, RETURN);
			CFG_nodet& new_node = add_node(return_node);
			instructions_to_nodes[it] = &new_node;
			if(NULL == entry_node)
			{
				entry_node = &new_node;
			}
		} else {
			CFG_nodet& new_node = add_node(CFG_nodet(*it));
			instructions_to_nodes[it] = &new_node;
			if(NULL == entry_node)
			{
				entry_node = &new_node;
			}
		}

	}

	/* Add edges to the CFG nodes according to the
	 * successor relationships between instructions
	 */
	for(goto_programt::targett
			instructions_it = program.instructions.begin();
			instructions_it != program.instructions.end();
			instructions_it++)
	{
		if((instructions_it->type == END_FUNCTION) || (instructions_it->type == RETURN))
		{
			/* A RETURN instruction has no CFG successors */
			assert(NULL == instructions_to_nodes[instructions_it]->successor_next && NULL == instructions_to_nodes[instructions_it]->successor_jump);
			continue;
		}

		/* Get the next instruction */
		goto_programt::targett next_instruction = get_following_instruction(instructions_it);
		assert(next_instruction != program.instructions.end());

		CFG_nodet* node = instructions_to_nodes[instructions_it];

		if(!(((node->type) == GOTO) && ((node->jump_condition) == true_exprt())))
		{
			/* We populate the "successor_next" field, unless the node is an unconditional jump */
			node->successor_next = instructions_to_nodes[next_instruction];
		}

		if((instructions_it->type == GOTO) && (node->jump_condition != false_exprt())) {
			/* We add a 'jump' successor to the current CFG node provided that the node
			 * is a GOTO, and the guard for the GOTO is not false
			 */
			assert(1 == instructions_it->targets.size());

			goto_programt::targett instruction_to_jump_to = instructions_it->targets.front();

			node->successor_jump = instructions_to_nodes[instructions_it->targets.front()];
		}

	}

	/* Remove unreachable parts of the CFG, and add predecessor information */
	update();

}


static int index_in_vector(const CFG_nodet* n, const CFGt::const_nodes_vectort* ordering)
{
	for(unsigned int i = 0; i < ordering->size(); i++)
	{
		if((*ordering)[i] == n)
		{
			return i;
		}
	}
	assert(false);
	return -1;
}

static void output_single_node(const CFG_nodet& node,
			std::ostream& out, const namespacet& ns, const CFGt::const_nodes_vectort* ordering, bool show_predecessors)
{
	if(NULL == ordering)
	{
		out << (&node);
	} else {
		out << index_in_vector(&node, ordering);
	}

	out << ": " << node.type << "  ";

	if(node.type == ASSERT || node.type == ASSUME)
	{
		out << from_expr(ns, "", node.reasoning_guard) << std::endl;
	} else if(node.type != GOTO && node.type != SKIP && node.type != END_FUNCTION) {
		out << from_expr(ns, "", node.code);
	} else {
		out << std::endl;
	}

	out << "    ";

	if(NULL != node.successor_jump)
	{
		out << "if(" << from_expr(ns, "", node.jump_condition) << ") GOTO ";

		if(NULL == ordering)
		{
			out << node.successor_jump;
		} else {
			out << index_in_vector(node.successor_jump, ordering);
		}

		out << " ELSE ";
	}

	if(NULL == node.successor_next) {
		out << "EXIT";
	} else {
		out << "GOTO ";
		if(NULL == ordering)
		{
			out << node.successor_next;
		} else {
			out << index_in_vector(node.successor_next, ordering);
		}
	}

	out << std::endl;

	node.output_special_info(out);

	if(show_predecessors)
	{
		out << "Predecessors:";
		for(std::set<CFG_nodet*>::const_iterator
				predecessor_it = node.predecessors.begin();
				predecessor_it != node.predecessors.end();
				predecessor_it++)
		{
			output_single_node(**predecessor_it, out, ns, ordering, false);
		}
		out << std::endl;
	}
}

void CFGt::output_node(
		const CFG_nodet& node,
		std::ostream& out, bool show_predecessors) const
{
	namespacet ns(context);
	output_single_node(node, out, ns, &ordered_nodes, show_predecessors);
}


static void output_nodes(const CFGt::const_nodes_vectort& ordered_nodes,
				const class namespacet &ns,
				std::ostream& out, bool show_predecessors)
{
	for(CFGt::const_nodes_vectort::const_iterator it = ordered_nodes.begin(); it != ordered_nodes.end(); it++)
	{
		output_single_node(**it, out, ns, &ordered_nodes, show_predecessors);
	}

}


void CFGt::output(
		std::ostream& out, bool show_predecessors) const
{
	output_nodes(ordered_nodes, namespacet(context), out, show_predecessors);
}


void CFGt::to_goto_program(
    goto_programt& program, 
    std::map<goto_programt::const_targett, std::pair<unsigned int, unsigned int> >* loop_header_instruction_points,
    std::map<const CFG_nodet*, goto_programt::const_targett>* node_to_target) const
{
	program.instructions.clear();

	if(NULL != loop_header_instruction_points)
	{
		loop_header_instruction_points->clear();
	}

	std::map<goto_programt::targett, const CFG_nodet*> instructions_to_nodes;
	std::map<const CFG_nodet*, goto_programt::targett> nodes_to_instructions;

	for(const_nodes_vectort::const_iterator nodes_it = ordered_nodes.begin(); nodes_it != ordered_nodes.end(); nodes_it++)
	{

		goto_programt::targett inst = program.add_instruction();

		check_cfg_point(inst, *nodes_it, loop_header_instruction_points);

		instructions_to_nodes[inst] = *nodes_it;
		nodes_to_instructions[*nodes_it] = inst;

		inst->code = (*nodes_it)->code;
		inst->function = (*nodes_it)->function;
		inst->location = (*nodes_it)->location;
		inst->type = (*nodes_it)->type;

		if(inst->type == ASSERT || inst->type == ASSUME)
		{
			inst->guard = (*nodes_it)->reasoning_guard;
		}

		if(inst->type == GOTO)
		{
			inst->guard = (*nodes_it)->jump_condition;
		}

		// If we find a CFG node that has no successor, its instruction must be followed by a return instruction
		if((NULL == (*nodes_it)->successor_next) && (NULL == (*nodes_it)->successor_jump))
		{
			assert(RETURN == (*nodes_it)->type);
		}

	}


	for(const_nodes_vectort::const_iterator nodes_it = ordered_nodes.begin(); nodes_it != ordered_nodes.end(); nodes_it++)
	{
		const CFG_nodet* node = *nodes_it;
		goto_programt::targett inst = nodes_to_instructions[node];

		if(node->type == GOTO) {
			assert(inst->targets.empty());
			assert(node->successor_jump != NULL);
			inst->targets.push_back( nodes_to_instructions[node->successor_jump] );
		}

		goto_programt::targett next_inst = inst;
		next_inst++;

		if(next_inst == program.instructions.end() && NULL != node->successor_next) {
			goto_programt::targett goto_instruction = program.add_instruction();
			goto_instruction->make_goto();
			goto_instruction->targets.push_back(nodes_to_instructions[node->successor_next]);
		} else if(next_inst != program.instructions.end() && instructions_to_nodes[next_inst] != node->successor_next
				&& NULL != node->successor_next) {
			goto_programt temp_program;
			temp_program.instructions.clear();
			goto_programt::targett goto_instruction = temp_program.add_instruction();
			goto_instruction->make_goto();
			goto_instruction->targets.push_back(nodes_to_instructions[node->successor_next]);
			program.instructions.splice(next_inst, temp_program.instructions);
		}

	}

	program.add_instruction(END_FUNCTION);

	program.update();

  if(node_to_target != NULL)
  {
    for(std::map<const CFG_nodet*, goto_programt::targett>::const_iterator 
          it = nodes_to_instructions.begin(); 
        it != nodes_to_instructions.end(); ++it)
    {
      (*node_to_target)[it->first] = it->second;
    }

  }

}


CFG_nodet& CFGt::append_node(CFG_nodet node)
{
	return append_node_ptr(new CFG_nodet(node));
}


CFG_nodet& CFGt::add_node(CFG_nodet node)
{
	return add_node_ptr(new CFG_nodet(node));
}


CFG_nodet& CFGt::append_node_ptr(CFG_nodet* node)
{
	if(NULL == last_node_added)
	{
		assert(NULL == entry_node);
		entry_node = node;
	} else {
		assert(NULL != entry_node);
		last_node_added->successor_next = node;
	}
	last_node_added = node;
	nodes.insert(node);
	return *node;
}


CFG_nodet& CFGt::add_node_ptr(CFG_nodet* node)
{
	if(NULL == entry_node)
	{
		assert(NULL == last_node_added);
		entry_node = node;
	}
	last_node_added = node;
	nodes.insert(node);
	return *node;
}


void CFGt::hoist_declarations()
{

	CFG_nodet* first_non_decl = entry_node;
	while(DECL == first_non_decl->type)
	{
		first_non_decl = first_non_decl->successor_next;
	}

	nodes_vectort processed_declarations;

	bool changed = true;
	while(changed)
	{
		changed = false;
		for(nodes_sett::iterator it = nodes.begin(); it != nodes.end(); it++)
		{
			if((DECL == (*it)->type) && (processed_declarations.end() == std::find(processed_declarations.begin(), processed_declarations.end(), *it)))
			{
				changed = true;
				processed_declarations.push_back(*it);
				nodes_mappingt patchup_map;
				patchup_map[*it] = (*it)->successor_next;
				patchup_pointers(patchup_map);
				break;
			}
		}
	}

	for(unsigned int i = 0; i < processed_declarations.size(); i++)
	{
		if(0 == i)
		{
			entry_node = processed_declarations[i];
		} else {
			processed_declarations[i-1]->successor_next = processed_declarations[i];
		}
		if(processed_declarations.size() - 1 == i)
		{
			processed_declarations[i]->successor_next = first_non_decl;
		}
	}

	update();

}



void CFGt::remove_self_loops()
{
	/* Loop analysis techniques can be made simpler if we are able to assume no
	 * self-looping CFG nodes.  These can be removed by adding intermediate "SKIP"
	 * nodes -- this method does such removal
	 */

	for(nodes_sett::iterator
			it = nodes.begin();
			it != nodes.end();
			it++) {
		if((*it)->successor_next == *it) {
			CFG_nodet& skip_node = add_node(CFG_nodet(code_skipt(), (*it)->function, (*it)->location, SKIP));
			skip_node.successor_next = *it;
			(*it)->successor_next = &skip_node;
		}
		if((*it)->successor_jump == *it) {
			CFG_nodet& skip_node = add_node(CFG_nodet(code_skipt(), (*it)->function, (*it)->location, SKIP));
			skip_node.successor_next = *it;
			(*it)->successor_jump = &skip_node;
		}
	}
}




void CFGt::add_returns()
{
	for(nodes_sett::iterator
			it = nodes.begin();
			it != nodes.end();
			it++) {
		if(RETURN != (*it)->type && NULL == (*it)->successor_next && NULL == (*it)->successor_jump) {
			CFG_nodet& return_node = add_node(CFG_nodet(code_returnt(), (*it)->function, (*it)->location, RETURN));
			if(GOTO == (*it)->type)
			{
				(*it)->successor_jump = &return_node;
			} else {
				(*it)->successor_next = &return_node;
			}
		}
	}
}




bool CFGt::all_non_back_edge_predecessors_ordered(
		const CFG_nodet* dest,
		const const_nodes_vectort& ordered,
		const dominator_infot& dominator_info) const {

	for(nodes_sett::const_iterator source = dest->predecessors.begin(); source != dest->predecessors.end(); source++)
	{
		if(dominator_info.is_back_edge(**source, *dest))
		{
			continue;
		}
		if(ordered.end() == std::find(ordered.begin(), ordered.end(), *source))
		{
			return false;
		}
	}

	return true;

}

void CFGt::order_nodes()
{

	dominator_infot dominator_info(*this);

	ordered_nodes.clear();

	assert(dominator_info.cfg_is_reducible(DFST_numberingt(*this)));

	nodest todo;
	todo.push_front(entry_node);

	unsigned int iterations_with_no_progress = 0;

	while(!todo.empty())
	{
		assert(iterations_with_no_progress < nodes.size());
		iterations_with_no_progress++;

		CFG_nodet* current = todo.front();
		todo.pop_front();

		if(!all_non_back_edge_predecessors_ordered(current, ordered_nodes, dominator_info))
		{
			todo.push_back(current);
		} else {
			// This node is next in the ordered_nodes, so plug it in
			current->id = ordered_nodes.size();
			ordered_nodes.push_back(current);
			iterations_with_no_progress = 0;

			// Add any successors if they are not already mapped or queued
			if((NULL != current->successor_next) && (ordered_nodes.end() == std::find(ordered_nodes.begin(), ordered_nodes.end(), current->successor_next)) && (todo.end() == find(todo.begin(), todo.end(), current->successor_next)))
			{
				todo.push_front(current->successor_next);
			}
			if((NULL != current->successor_jump) && (ordered_nodes.end() == std::find(ordered_nodes.begin(), ordered_nodes.end(), current->successor_jump)) && (todo.end() == find(todo.begin(), todo.end(), current->successor_jump)))
			{
				todo.push_front(current->successor_jump);
			}

		}
	}

}

void CFGt::order_nodes_raw()
{
	ordered_nodes.clear();

	ordered_nodes.push_back(entry_node);

	for(nodes_sett::iterator it = nodes.begin(); it != nodes.end(); it++)
	{
		if((*it) != entry_node)
		{
			ordered_nodes.push_back(*it);
		}
	}
}




bool CFGt::contains(const CFG_nodet& n) const
{
	/* Note that this does *not* take reachability into account */
	return nodes.end() != std::find(nodes.begin(), nodes.end(), (CFG_nodet*)&n);
}



void CFGt::calculate_prececessors()
{
	for(nodes_sett::iterator
			it = nodes.begin();
			it != nodes.end();
			it++)
	{
		(*it)->predecessors.clear();
	}

	for(nodes_sett::iterator
			it = nodes.begin();
			it != nodes.end();
			it++)
	{
		if(NULL != (*it)->successor_next)
		{
			(*it)->successor_next->predecessors.insert(*it);
		}

		if(NULL != (*it)->successor_jump)
		{
			(*it)->successor_jump->predecessors.insert(*it);
		}

	}

}


void CFGt::sanity_check() const {
	// Entry node has no predecessors
	// Every node's successors and predecessors must be in the CFG
	// A node's successors must be distinct
	// A node may not have more predecessors than the size of the CFG

	assert(entry_node->predecessors.size() == 0);

	for(CFGt::nodes_sett::const_iterator it = nodes.begin(); it != nodes.end(); it++)
	{
		if(NULL != (*it)->successor_next)
		{
			nodes.end() != std::find(nodes.begin(), nodes.end(), (*it)->successor_next);
		}

		if(NULL != (*it)->successor_jump)
		{
			nodes.end() != std::find(nodes.begin(), nodes.end(), (*it)->successor_jump);
		}

		if(NULL != (*it)->successor_next && NULL != (*it)->successor_jump)
		{
			assert((*it)->successor_next != (*it)->successor_jump);
		}

		assert((*it)->predecessors.size() <= size());

	}

}

void CFGt::update() {
	add_returns();
	remove_self_loops();
	collect_garbage();
	calculate_prececessors();
	order_nodes();
	assert(ordered_nodes.size() == nodes.size());
	sanity_check();
}

CFG_nodet& CFGt::get_initial()
{
  if(size() == 0)
    throw "get_initial called on empty CFG";
  return *entry_node;
}

const CFG_nodet& CFGt::get_initial() const
{
  if(size() == 0)
    throw "get_initial called on empty CFG";
  return *entry_node;
}




void CFGt::transform_to_monolithic_loop()
{
	loop_infot existing_loops(*this);

	if(existing_loops.num_loops() <= 1)
	{
		// No need to do transformation if there is only one, or even zero, loops
		return;
	}

	std::vector<CFG_nodet*> headers;
	for(std::list<loop_infot::loopt>::iterator it = existing_loops.loops.begin(); it != existing_loops.loops.end(); it++) {
		headers.push_back((CFG_nodet*)(it->header));
	}

	symbolt loop_to_jump_to;
	{
		// Add new declaration for variable
		loop_to_jump_to.base_name = "loop_to_jump_to";
		loop_to_jump_to.name = "__k_induction::" + loop_to_jump_to.base_name.as_string();
		loop_to_jump_to.type = uint_type();
		context.add(loop_to_jump_to);
		exprt loop_to_jump_to_expr = symbol_expr(loop_to_jump_to);
		CFG_nodet& loop_to_jump_to_decl = add_node(CFG_nodet(code_declt(loop_to_jump_to_expr),
				entry_node->function,
				entry_node->location,
				DECL));

		loop_to_jump_to_decl.successor_next = entry_node;
		entry_node = &loop_to_jump_to_decl;
	}

	CFG_nodet& monolithic_header = add_node(CFG_nodet(code_assumet(), entry_node->function, entry_node->location, ASSUME));
	monolithic_header.reasoning_guard = binary_relation_exprt(symbol_expr(loop_to_jump_to), "<", from_integer(headers.size(), uint_type()));

	std::vector<CFG_nodet*> replacement_headers;
	for(unsigned int i = 0; i < headers.size(); i++)
	{
		codet nil_code;
		nil_code.make_nil();
		replacement_headers.push_back(&(add_node(CFG_nodet(
				nil_code,
				existing_loops.outer_loops[0]->header->function,
				existing_loops.outer_loops[0]->header->location,
				GOTO))));
		if(0 == i)
		{
			monolithic_header.successor_next = replacement_headers[i];
		} else {
			replacement_headers[i-1]->successor_next = replacement_headers[i];
		}

		if(i == headers.size() - 1)
		{
			replacement_headers[i]->jump_condition = true_exprt();
		} else {
			replacement_headers[i]->jump_condition = equality_exprt(symbol_expr(loop_to_jump_to), from_integer(i, uint_type()));
		}
	}

	// Go through every node in the CFG.  If the node would have pointed to header i, then add a new node that
	// assigns i to loop_to_jump_to, and then jumps to the monolithic header.
	// Note that we *cannot* just make a single node for each loop that assigns to loop_to_jump_to: this would
	// result in multiple loops.
	for(nodes_sett::iterator it = nodes.begin(); it != nodes.end(); it++)
	{
		for(unsigned int i = 0; i < headers.size(); i++)
		{
			if((*it)->successor_next == headers[i])
			{
				CFG_nodet& assign_to_loop_to_jump_to = add_node(CFG_nodet(code_assignt(symbol_expr(loop_to_jump_to), from_integer(i, uint_type())), headers[i]->function, headers[i]->location, ASSIGN));
				assign_to_loop_to_jump_to.successor_next = &monolithic_header;
				(*it)->successor_next = &assign_to_loop_to_jump_to;
			}

			if((*it)->successor_jump == headers[i])
			{
				CFG_nodet& assign_to_loop_to_jump_to = add_node(CFG_nodet(code_assignt(symbol_expr(loop_to_jump_to), from_integer(i, uint_type())), headers[i]->function, headers[i]->location, ASSIGN));
				assign_to_loop_to_jump_to.successor_next = &monolithic_header;
				(*it)->successor_jump = &assign_to_loop_to_jump_to;
			}
		}
	}

	for(unsigned int i = 0; i < headers.size(); i++)
	{
		replacement_headers[i]->successor_jump = headers[i];
	}

	update();

	// Sanity check
	assert(1 == loop_infot(*this).num_loops());

}




goto_programt& find_main(goto_functionst& goto_functions, contextt& context)
{
	namespacet ns(context);

    for(goto_functionst::function_mapt::iterator
    		f_it = goto_functions.function_map.begin();
			;
			f_it++)
    {

    	if(f_it == goto_functions.function_map.end())
    	{
    	    throw "main symbol not found; please set an entry point";
    	}

    	/* It seems that the scheme for naming functions
    	 * internally has recently changed within CPROVER,
    	 * this this code may no longer be the most suitable
    	 */
		if(ns.lookup(f_it->first).base_name == config.main)
		{
			assert(f_it->second.body_available);
			return f_it->second.body;
		}
    }
    assert(false);

}

goto_programt& find_enclosing_main(goto_functionst& goto_functions, contextt& context)
{
	namespacet ns(context);

    for(goto_functionst::function_mapt::iterator
    		f_it = goto_functions.function_map.begin();
			;
			f_it++)
    {

    	if(f_it == goto_functions.function_map.end())
    	{
    	    throw "main symbol not found; please set an entry point";
    	}

    	/* It seems that the scheme for naming functions
    	 * internally has recently changed within CPROVER,
    	 * this this code may no longer be the most suitable
    	 */
		if(ns.lookup(f_it->first).base_name == "")
		{
			assert(f_it->second.body_available);
			return f_it->second.body;
		}
    }
    assert(false);

}



unsigned int CFGt::size() const
{
	return nodes.size();
}



CFGt::~CFGt()
{
	for(nodes_sett::iterator it = nodes.begin(); it != nodes.end(); it++)
	{
		delete *it;
	}
}


const CFGt::const_nodes_vectort& CFGt::get_ordered_nodes() const
{
	return ordered_nodes;
}

CFGt::nodes_sett::const_iterator CFGt::begin() const
{
	return nodes.begin();
}

CFGt::nodes_sett::const_iterator CFGt::end() const
{
	return nodes.end();
}

const CFG_nodet& CFGt::get_last_added_node() const
{
	assert(NULL != last_node_added);
	return *last_node_added;
}

CFG_nodet& CFGt::get_last_added_node()
{
	assert(NULL != last_node_added);
	return *last_node_added;
}


void CFGt::collect_garbage()
{
	nodes_sett reachable;

	nodest todo;
	todo.push_back(entry_node);

	while(!todo.empty())
	{
		CFG_nodet* current = todo.front();
		todo.pop_front();
		reachable.insert(current);
		if(NULL != current->successor_next && reachable.end() == reachable.find(current->successor_next) &&
				todo.end() == std::find(todo.begin(), todo.end(), current->successor_next))
		{
			todo.push_back(current->successor_next);
		}
		if(NULL != current->successor_jump && reachable.end() == reachable.find(current->successor_jump) &&
				todo.end() == std::find(todo.begin(), todo.end(), current->successor_jump))
		{
			todo.push_back(current->successor_jump);
		}
	}

	nodes_sett to_be_deleted;

	for(nodes_sett::iterator it = nodes.begin(); it != nodes.end(); it++)
	{
		if(reachable.end() == reachable.find(*it))
		{
			delete *it;
			to_be_deleted.insert(*it);
		}
	}

	for(nodes_sett::iterator it = to_be_deleted.begin(); it != to_be_deleted.end(); it++)
	{
		nodes.erase(std::find(nodes.begin(), nodes.end(), *it));
	}

}



void CFGt::unwind_loop(const CFG_nodet* header, const loop_infot& loop_info, unsigned int unwind_count)
{
	if(0 == unwind_count)
	{
		return;
	}
	const loop_infot::loopt* the_loop = NULL;
	for(std::list<loop_infot::loopt>::const_iterator it = loop_info.loops.begin(); it != loop_info.loops.end(); it++)
	{
		if(header == it->header)
		{
			the_loop = &(*it);
			break;
		}
	}
	assert(NULL != the_loop);

	nodes_sett non_loop_nodes;
	for(nodes_sett::iterator it = nodes.begin(); it != nodes.end(); it++)
	{
		if(!the_loop->contains(**it))
		{
			non_loop_nodes.insert(*it);
		}
	}

	nodes_vectort new_headers;
	std::vector<nodes_sett> new_nodes;
	for(unsigned int i = 0; i < unwind_count; i++)
	{
		assert(new_nodes.size() == i);
		new_nodes.push_back(nodes_sett());
		nodes_mappingt patchup_map;
		for(nodes_const_sett::iterator it = the_loop->begin(); it != the_loop->end(); it++)
		{
			CFG_nodet& new_node = add_node(CFG_nodet(**it));
			new_nodes[i].insert(&new_node);
			if(*it == header)
			{
				assert(new_headers.size() == i);
				new_headers.push_back(&new_node);
			} else {
				patchup_map[*it] = &new_node;
			}
		}
		patchup_pointers_in_nodes(new_nodes[i], patchup_map);
		if(i > 0)
		{
			nodes_mappingt header_patchup_map;
			header_patchup_map[header] = new_headers[i];
			patchup_pointers_in_nodes(new_nodes[i-1], header_patchup_map);
		}
	}

	nodes_mappingt final_patchup_map;
	final_patchup_map[header] = new_headers[0];
	patchup_pointers_in_nodes(non_loop_nodes, final_patchup_map);

	update();

}




void CFGt::check_cfg_point(goto_programt::const_targett inst, const CFG_nodet* node, std::map<goto_programt::const_targett, std::pair<unsigned int, unsigned int> >* loop_header_instruction_points) const
{
	return;
}

void CFGt::instrument_with_guards(
  const std::map<const CFG_nodet*, exprt>& instruction_to_invariant, 
  bool use_assert)
{
		for(const_nodes_vectort::const_iterator it = get_ordered_nodes().begin();
				it != get_ordered_nodes().end();
	      it++)
		{
      std::map<const CFG_nodet*, exprt>::const_iterator 
        find_it = instruction_to_invariant.find(*it);

      if(find_it == instruction_to_invariant.end())
        continue;

			CFG_nodet& instr_node = 
        use_assert ? 
          add_node(
            CFG_nodet(
              code_assertt(), 
              (*it)->function, 
              (*it)->location, ASSERT)) 
          : add_node(
            CFG_nodet(
              code_assumet(), 
              (*it)->function, 
              (*it)->location, ASSUME));

			instr_node.reasoning_guard = find_it->second;
			CFGt::nodes_mappingt patchup_map;
			patchup_map[*it] = &instr_node;
			patchup_pointers(patchup_map);
			instr_node.successor_next = (CFG_nodet*)*it;
		}

		update();

}
