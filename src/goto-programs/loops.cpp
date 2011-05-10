/*
 * loops.cpp
 *
 *  Created on: August 18, 2010
 *      Author: Alastair Donaldson
 */

#include <ansi-c/expr2c.h>

#include "loops.h"


static void insert_on_stack(const CFG_nodet& m, CFGt::nodes_const_sett & loop,
		std::vector<const CFG_nodet*> & stack)
{

	if(loop.end() != loop.find(&m))
	{
		return;
	}

	loop.insert(&m);

	stack.push_back(&m);

}

/* This is the algorithm of Fig. 10.15 of the Dragon book */
void loop_infot::compute_loop_nodes_for_back_edge(
		const CFG_nodet& n,
		const CFG_nodet& d,
		CFGt::nodes_const_sett & loop)
{

	std::vector<const CFG_nodet*> stack;

	loop.insert(&d);

	insert_on_stack(n, loop, stack);

	while(!stack.empty())
	{

		const CFG_nodet& m = *(stack.back());
		stack.pop_back();

		for(std::set<CFG_nodet*>::iterator
			it = m.predecessors.begin();
			it != m.predecessors.end();
			it++)
		{
			insert_on_stack(**it, loop, stack);
		}
	}

}


loop_infot::loop_infot(const CFGt& cfg)
{
	dominator_infot dominator_info(cfg);

	/* Our loop analysis infrastructure is only designed for reducible control-flow graphs,
	 * so check that we have one
	 */
	{
		DFST_numberingt dfst_numbering(cfg);
		assert(dominator_info.cfg_is_reducible(dfst_numbering));
	}

	for(CFGt::const_nodes_vectort::const_iterator cfg_it = cfg.get_ordered_nodes().begin(); cfg_it != cfg.get_ordered_nodes().end(); cfg_it++)
	{
	    const CFG_nodet& d = **cfg_it;

	    loop_infot::loopt* loop_headed_at_current_node = NULL;

	    for(std::set<CFG_nodet*>::const_iterator
		    predecessor_it = d.predecessors.begin();
    		predecessor_it != d.predecessors.end();
    		predecessor_it++)
	    {
	    	/* Getting into notation of Dragon book: */

	    	const CFG_nodet& n = **predecessor_it;

			/* We have an edge of the form n -> d
			 *
			 * Need to check whether d dominates n
			 */

	    	if(dominator_info.is_back_edge(n, d))
	    	{
	    		CFGt::nodes_const_sett loop_nodes = CFGt::nodes_const_sett();

	    		compute_loop_nodes_for_back_edge(n, d, loop_nodes);

	    		if(NULL == loop_headed_at_current_node)
	    		{
	    			// This is the first loop detected for this header
				loopt new_loop(&d, loop_nodes, &cfg);
	    			loops.push_back(new_loop);
				loop_headed_at_current_node = &loops.back();


	    		} else {
	    			// There are already loops at this header: merge the new loop with these loops
	    			loop_headed_at_current_node->add_nodes(loop_nodes);
	    		}


		    }

		}

	}

	organize_loops(cfg);

}


loop_infot::loopt* loop_infot::get_closest_containing_loop(const CFG_nodet* n) const
{
	std::map<const CFG_nodet*, loopt*>::const_iterator it = closest_containing_loop.find(n);

	if(it == closest_containing_loop.end())
	{
		return NULL;
	}

	return it->second;

}

loop_infot::loopt* loop_infot::get_largest_containing_loop(const CFG_nodet* n) const
{
	for(unsigned int i = 0; i < outer_loops.size(); i++)
	{
		if(outer_loops[i]->contains(*n))
		{
			return outer_loops[i];
		}
	}
	return NULL;
}



void loop_infot::organize_loops(const CFGt& cfg)
{
	if(loops.empty())
	{
		return;
	}

	/* First, give each loop a parent if it has one */
	for(std::list<loop_infot::loopt>::iterator
			it1 = loops.begin();
			it1 != loops.end();
			it1++)
	{
	  std::list<loop_infot::loopt>::iterator
	    it2 = it1;
		for(it2++;
			it2 != loops.end();
			it2++)
		{
			loop_infot::loopt & loop1 = *it1;
			loop_infot::loopt & loop2 = *it2;

			if( loop1.contains(loop2) )
			{
				loop2.candidate_parent(loop1);
			} else if( loop2.contains(loop1) ) {
				loop1.candidate_parent(loop2);
			} else {
				assert ( loop_infot::loopt::disjoint (loop1, loop2 ) );
			}

		}

	}

	/* Next, assign immediate children to every loop, and work out the outer and inner loops */
	for(std::list<loop_infot::loopt>::iterator
			it1 = loops.begin();
			it1 != loops.end(); // Note that we don't use end() - 1 here as we need to consider all loops when working out inner and outer loops
			it1++)
	{
		loop_infot::loopt & loop1 = *it1;

		if(NULL == loop1.parent)
		{
			outer_loops.push_back(&loop1);
		}

		std::list<loop_infot::loopt>::iterator it2 = it1;

		for(it2++;
			it2 != loops.end();
			it2++)
		{
			loop_infot::loopt & loop2 = *it2;

			if( loop2.parent == &loop1 )
			{
				loop1.children.push_back(&loop2);
			}
		}

		if(loop1.children.empty())
		{
			inner_loops.push_back(&loop1);
		}

	}

	/* Finally, compute mapping which assigns each instruction to its nearest loop */
	for(CFGt::const_nodes_vectort::const_iterator it = cfg.get_ordered_nodes().begin(); it != cfg.get_ordered_nodes().end(); it++)
	{

		closest_containing_loop[*it] = NULL;

		for(std::vector<loop_infot::loopt *>::iterator
				inner_loop_it = inner_loops.begin();
				inner_loop_it != inner_loops.end();
				inner_loop_it++)
		{
			loop_infot::loopt * current_loop = *inner_loop_it;

			while(NULL != current_loop)
			{
				if(current_loop->contains(**it))
				{
					if((NULL == closest_containing_loop[*it]) || closest_containing_loop[*it]->contains(*current_loop))
					{
						closest_containing_loop[*it] = current_loop;
					}
					break;
				}

				current_loop = current_loop->parent;
			}

		}

	}

}


void loop_infot::loopt::candidate_parent( loopt& other )
{
	/* Set 'other' as parent if we don't have one.  Otherwise,
	 * we'd like 'other' as parent if our parent contains other,
	 * i.e. we have this <= other <= parent.
	 */
	if((NULL == parent) || (parent->contains(other)))
	{
		parent = &other;
	}
}


bool loop_infot::loopt::contains( const loopt& other) const
{
	for(CFGt::nodes_const_sett::iterator
			it = other.nodes.begin();
			it != other.nodes.end();
			it++)
	{
		bool found = false;
		for(CFGt::nodes_const_sett::iterator
				it2 = this->nodes.begin();
				it2 != this->nodes.end();
				it2++)
		{
			if( (*it) == (*it2) )
			{
				found = true;
				break;
			}
		}

		if(!found)
		{
			return false;
		}

	}

	return true;
}

bool loop_infot::loopt::contains( const CFG_nodet& inst) const
{
	return nodes.end() != nodes.find(&inst);
}

bool loop_infot::loopt::disjoint ( loopt& loop1, loopt& loop2 )
{
	for(CFGt::nodes_const_sett::iterator
			it = loop1.nodes.begin();
			it != loop1.nodes.end();
			it++)
	{
		for(CFGt::nodes_const_sett::iterator
				it2 = loop2.nodes.begin();
				it2 != loop2.nodes.end();
				it2++)
		{
			if( (*it) == (*it2) )
			{
				return false;
			}
		}

	}

	return true;

}



void loop_infot::loopt::add_nodes(CFGt::nodes_const_sett nodes)
{
	for(CFGt::nodes_const_sett::iterator it = nodes.begin(); it != nodes.end(); it++)
	{
		this->nodes.insert(*it);
	}
}


unsigned int loop_infot::loopt::num_nodes() const
{
	return nodes.size();
}


bool loop_infot::loopt::is_new_post_node(std::vector<const CFG_nodet*>& post_nodes, CFG_nodet* n) const
{
	return (NULL != n) && !(this->contains(*n)) && (post_nodes.end() == find(post_nodes.begin(), post_nodes.end(), n));
}


void loop_infot::loopt::calculate_post_nodes(std::vector<const CFG_nodet*>& result) const
{
	for(CFGt::nodes_const_sett::const_iterator it = nodes.begin(); it != nodes.end(); it++)
	{
		if(is_new_post_node(result, (*it)->successor_next))
		{
			result.push_back((*it)->successor_next);
		}
		if(is_new_post_node(result, (*it)->successor_jump))
		{
			result.push_back((*it)->successor_jump);
		}
	}
}



loop_infot::loopt::loopt(const CFG_nodet* header, CFGt::nodes_const_sett nodes, const CFGt* cfg) : header(header), cfg(cfg)
{
	this->add_nodes(nodes);
	this->parent = NULL;

}


std::ostream& operator<<(std::ostream& os, const loop_infot& loop_info)
{

	for(std::vector<loop_infot::loopt *>::const_iterator
			outer_loop_it = loop_info.outer_loops.begin();
			outer_loop_it != loop_info.outer_loops.end();
			outer_loop_it++)
	{
		os << (**outer_loop_it);
	}

	return os;

}



static void blanks(std::ostream& os, const int num)
{
	for(int i=0; i<num; ++i)
	{
		os << " ";
	}

}


std::ostream& operator<<(std::ostream& os, const loop_infot::loopt& loop)
{
	static unsigned indent = 0;
	const int indent_size = 4;

	blanks(os, indent);
	os << "[" << std::endl;
	blanks(os, indent);
	os << "    header:\n";
	loop.cfg->output_node(*(loop.header), os);
	os << std::endl;
	blanks(os, indent);
	os << "    nodes:\n";

	for(CFGt::nodes_const_sett::const_iterator
			it = loop.nodes.begin();
			it != loop.nodes.end();
			it++)
	{
		os << " ";
		loop.cfg->output_node(**it, os);
	}
	os << std::endl;

	if(!loop.children.empty())
	{
		blanks(os, indent);
		os << "    children:" << std::endl;

		indent += indent_size;

		for(std::vector<loop_infot::loopt *>::const_iterator
				it = loop.children.begin();
				it != loop.children.end();
				it++)
		{
			os << (**it) << std::endl;
		}

		indent -= indent_size;

	}

	blanks(os, indent);
	os << "]" << std::endl;

	return os;

}


unsigned int loop_infot::num_loops() const
{
	return this->loops.size();
}


bool loop_infot::is_inner_loop(const loopt* loop) const
{
	if(NULL == loop)
	{
		return false;
	}

	for(std::vector<loop_infot::loopt*>::const_iterator
			it = inner_loops.begin();
			it != inner_loops.end();
			it++)
	{
		if((*it) == loop)
		{
			return true;
		}

	}

	return false;

}


static bool is_unexplored_descendent(CFG_nodet* node, const loop_infot::loopt& loop, std::set<const CFG_nodet*>& visited, std::list<const CFG_nodet*>& queue)
{
	return NULL != node &&
			loop.contains(*node) &&
			loop.header != node &&
			visited.end() == visited.find(node) &&
			queue.end() == std::find(queue.begin(), queue.end(), node);
}

bool loop_infot::loopt::on_critical_path(const CFG_nodet& n) const
{
	std::set <const CFG_nodet*> visited;
	std::list <const CFG_nodet*> queue;

	dominator_infot dominator_info(*cfg);

	queue.push_back(&n);

	while(!queue.empty())
	{
		const CFG_nodet* current = queue.front();
		queue.pop_front();
		visited.insert(current);

		if(!dominator_info.dominates(n, *current))
		{
			return false;
		}

		if(is_unexplored_descendent(current->successor_next, *this, visited, queue))
		{
			queue.push_back(current->successor_next);
		}

		if(is_unexplored_descendent(current->successor_jump, *this, visited, queue))
		{
			queue.push_back(current->successor_jump);
		}
	}

	return true;
}

void loop_infot::loopt::find_simple_induction_variables(std::set<induction_variablet>& result)
{
	// First, find "critical path" through loop: nodes which *must* be executed on any loop iteration
	CFGt::nodes_const_sett critical_path;

	for(CFGt::nodes_const_sett::const_iterator it = nodes.begin(); it != nodes.end(); it++)
	{
		if(on_critical_path(**it))
		{
			critical_path.insert(*it);
		}
	}

	for(CFGt::nodes_const_sett::const_iterator it = nodes.begin(); it != nodes.end(); it++)
	{
		if(NULL != (*it)->successor_next && NULL != (*it)->successor_jump && ((!contains(*((*it)->successor_next))) || !contains(*((*it)->successor_jump))))
		{
			if(critical_path.end() == critical_path.find(*it))
			{
				std::cout << "Exit from loop not on critical path; not interested\n";
				return;
			}
		}

	}



	std::cout << "Loop is: " << (*this);

	std::map<symbol_exprt, int> num_increments_on_critical_path;
	std::map<symbol_exprt, exprt> increment_value;
	std::set<symbol_exprt> symbols_modified_non_incrementally_on_critical_path;
	std::set<symbol_exprt> symbols_modified_off_critical_path;

	for(CFGt::nodes_const_sett::iterator it = critical_path.begin(); it != critical_path.end(); it++)
	{
		if(ASSIGN == (*it)->type) {
			exprt lhs = (*it)->code.op0();
			exprt rhs = (*it)->code.op1();
			if(lhs.id() == ID_symbol)
			{
				symbol_exprt lhs_as_symbol = to_symbol_expr(lhs);
				if(rhs.id() == ID_plus && rhs.op0() == lhs && rhs.op1().id() == ID_constant) {
					if(num_increments_on_critical_path.end() == num_increments_on_critical_path.find(lhs_as_symbol))
					{
						num_increments_on_critical_path[lhs_as_symbol] = 1;
						increment_value[lhs_as_symbol] = rhs.op1();
					} else {
						num_increments_on_critical_path[lhs_as_symbol] = num_increments_on_critical_path[lhs_as_symbol] + 1;
					}
				} else {
					symbols_modified_non_incrementally_on_critical_path.insert(lhs_as_symbol);
				}
			}
		}

	}

	for(CFGt::nodes_const_sett::iterator it = this->nodes.begin(); it != this->nodes.end(); it++)
	{
		if(critical_path.end() == critical_path.find(*it))
		{
			if(ASSIGN == (*it)->type && (*it)->code.op0().id() == ID_symbol)
			{
				symbols_modified_off_critical_path.insert(to_symbol_expr((*it)->code.op0()));
			}
		}
	}

	std::map<symbol_exprt, exprt> initial_value;

	const CFG_nodet* n = NULL;

	for(CFGt::nodes_sett::iterator it = this->header->predecessors.begin(); it != this->header->predecessors.end(); it++)
	{
		if(!(this->contains(**it)))
		{
			if(NULL != n)
			{
				n = NULL;
				break;
			} else {
				n = *it;
			}
		}

	}

	while(NULL != n && n->predecessors.size() == 1)
	{
		if(ASSIGN == n->type && n->code.op0().id() == ID_symbol)
		{
			if(initial_value.end() == initial_value.find(to_symbol_expr(n->code.op0())))
			{
				initial_value[to_symbol_expr(n->code.op0())] = n->code.op1();
			}
		}
		n = *(n->predecessors.begin());
	}




	for(std::map<symbol_exprt, int>::iterator it = num_increments_on_critical_path.begin(); it != num_increments_on_critical_path.end(); it++)
	{
		if(1 == it->second && symbols_modified_non_incrementally_on_critical_path.end() == symbols_modified_non_incrementally_on_critical_path.find(it->first)
				&& symbols_modified_off_critical_path.end() == symbols_modified_off_critical_path.find(it->first)
				/*&& initial_value.end() != initial_value.find(it->first)*/)
		{
			namespacet ns(this->cfg->context);
			std::cout << "Found an induction variable: ";
			std::cout << expr2c(it->first, ns);
			std::cout << ", its initial value is " << expr2c(initial_value[it->first], ns);
		    std::cout << " and its increment is ";
			std::cout << expr2c(increment_value[it->first], ns) << "\n";
		}

	}






}

