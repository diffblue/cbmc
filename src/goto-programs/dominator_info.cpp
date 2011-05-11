/*
 * dominator_info.cpp
 *
 *  Created on: August 18, 2010
 *      Author: Alastair Donaldson
 */


#include "dominator_info.h"


/* This is the algorithm in Fig. 10.52 of the Dragon book.
 *
 */
dominator_infot::dominator_infot(const CFGt& cfg) : the_cfg(cfg)
{
	// Visiting nodes in a depth-first order *drastically* speeds up
	// convergence speed for dominator detection

	DFST_numberingt numbering(the_cfg);

	std::vector<const CFG_nodet*> depth_first_ordered_nodes(the_cfg.size());
	for(unsigned int i = 0; i < depth_first_ordered_nodes.size(); i++)
	{
		depth_first_ordered_nodes[i] = NULL;
	}
	for(CFGt::nodes_sett::const_iterator it = the_cfg.begin(); it != the_cfg.end(); it++)
	{
		depth_first_ordered_nodes[numbering.get_number(*it)] = *it;
	}
	for(unsigned int i = 0; i < depth_first_ordered_nodes.size(); i++)
	{
		assert(depth_first_ordered_nodes[i] != NULL);
	}

	dominators_of.clear();

	CFGt::nodes_const_sett N;
	for(CFGt::nodes_sett::const_iterator it = the_cfg.begin(); it != the_cfg.end(); it++)
	{
		N.insert(*it);
	}

	const CFG_nodet& n_0 = cfg.get_initial();

	dominators_of[&n_0] = CFGt::nodes_const_sett();
	dominators_of[&n_0].insert(&n_0);

	for(CFGt::nodes_sett::const_iterator
			it = cfg.begin();
			it != cfg.end();
			it++)
	{

		if(&n_0 != *it)
		{
			dominators_of[*it] = N;
		}
	}

	bool changed = true;
	while(changed)
	{

		changed = false;

		for(unsigned int i = 0; i < depth_first_ordered_nodes.size(); i++)
		{
			const CFG_nodet* node = depth_first_ordered_nodes[i];

			if(&n_0 != node)
			{

				CFGt::nodes_const_sett intersection_of_incoming_dominators;

				for(std::set<CFG_nodet*>::const_iterator
					it2 = node->predecessors.begin();
					it2 != node->predecessors.end();
					it2++)
				{
					if(node->predecessors.begin() == it2)
					{
						intersection_of_incoming_dominators = dominators_of[*it2];
					} else {
						CFGt::nodes_const_sett intersection;
						#ifndef _WIN32 // the following isn't widely available
						set_intersection(
								intersection_of_incoming_dominators.begin(),
								intersection_of_incoming_dominators.end(),
								dominators_of[*it2].begin(),
								dominators_of[*it2].end(),
								std::insert_iterator<CFGt::nodes_const_sett >(intersection, intersection.begin()));
                                                #endif

						intersection_of_incoming_dominators = intersection;
					}

				}

				intersection_of_incoming_dominators.insert(node);

				if(dominators_of[node] != intersection_of_incoming_dominators) {
					dominators_of[node] = intersection_of_incoming_dominators;
					changed = true;
				}

			}

		}

	}

}



std::ostream& operator<<(std::ostream& os, const dominator_infot& dom)
{
	for(std::map<const CFG_nodet*, CFGt::nodes_const_sett >::const_iterator i = dom.dominators_of.begin(); i != dom.dominators_of.end(); i++)
	{
		dom.the_cfg.output_node(*(i->first), os);

		os << " dominated by {\n  ";
		for(CFGt::nodes_const_sett::const_iterator j = i->second.begin(); j != i->second.end(); j++)
		{
			if(j != i->second.begin()) {
				os << ", ";
			}

			dom.the_cfg.output_node(**j, os);

		}

		os << " }\n\n";

	}


	return os;
}


bool dominator_infot::dominates(const CFG_nodet& first, const CFG_nodet& second) const
{
	dominator_mapt::const_iterator dominators_of_second = dominators_of.find(&second);
	assert(dominators_of_second != dominators_of.end());
	return dominators_of_second->second.find(&first) != dominators_of_second->second.end();
}

bool dominator_infot::is_back_edge(const CFG_nodet& source, const CFG_nodet& dest) const
{
	return dominates(dest, source);
}

bool dominator_infot::cfg_is_reducible(const DFST_numberingt& dfst)
{
	for(CFGt::nodes_sett::const_iterator
			cfg_it = the_cfg.begin();
			cfg_it != the_cfg.end();
			cfg_it++)
	{
		const CFG_nodet& d = **cfg_it;

	    for(std::set<CFG_nodet*>::const_iterator
		    predecessor_it = d.predecessors.begin();
    		predecessor_it != d.predecessors.end();
    		predecessor_it++)
	    {
	    	const CFG_nodet& n = **predecessor_it;

			/* We have an edge of the form n -> d
			 * Need to check whether the edge is retreating
			 */

	    	if(dfst.is_retreating(n, d))
	    	{
	    		if(!is_back_edge(n, d))
	    		{
	    			return false;
	    		}
	    	}
		}

	}
	return true;
}
