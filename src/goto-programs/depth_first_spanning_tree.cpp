/*
 * depth_first_spanning_tree.cpp
 *
 *  Created on: August 18, 2010
 *      Author: Alastair Donaldson
 */

#include "depth_first_spanning_tree.h"

int DFST_numberingt::search(const CFG_nodet& n, CFGt::nodes_const_sett& visited, int c)
{
	assert(c >= 0);
	if(n == the_cfg.get_initial()) {
		assert(c == (int)the_cfg.size());
	} else {
		assert(c <= (int)the_cfg.size());
	}

	/* The node should not yet have been visited */
	assert(visited.end() == visited.find(&n));

	visited.insert(&n);

	if((NULL != n.successor_next) && (visited.end() == visited.find(n.successor_next)))
	{
		c = search(*(n.successor_next), visited, c);
	}

	if((NULL != n.successor_jump) && (visited.end() == visited.find(n.successor_jump)))
	{
		c = search(*(n.successor_jump), visited, c);
	}

	c--;
	dfn[&n] = c;

	/* c should remain non-negative, and should be zero only on leaving
	 * the root node
	 */
	if(n == the_cfg.get_initial()) {
		assert(0 == c);
	} else {
		assert(c > 0);
	}

	return c;

}

DFST_numberingt::DFST_numberingt(const CFGt& cfg) : the_cfg(cfg)
{
	CFGt::nodes_const_sett visited;
	search(the_cfg.get_initial(), visited, the_cfg.size());
}

std::ostream& operator<<(std::ostream& os, const DFST_numberingt& dfst)
{
	for(CFGt::nodes_sett::const_iterator it = dfst.the_cfg.begin(); it != dfst.the_cfg.end(); it++)
	{
		dfst.the_cfg.output_node(**it, os, false);
		os << "  DFST number: " << ((DFST_numberingt&)dfst).dfn[*it]<< "\n";
	}

	return os;

}

bool DFST_numberingt::is_retreating(const CFG_nodet& d, const CFG_nodet& n) const
{
	std::map<const CFG_nodet*, unsigned int>::const_iterator it_n = dfn.find(&n);
	assert(it_n != dfn.end());

	std::map<const CFG_nodet*, unsigned int>::const_iterator it_d = dfn.find(&d);
	assert(it_d != dfn.end());

	return it_n->second <= it_d->second;
}


unsigned int DFST_numberingt::get_number(const CFG_nodet* n) const
{
	std::map<const CFG_nodet*, unsigned int>::const_iterator it_n = dfn.find(n);
	assert(it_n != dfn.end());
	return it_n->second;
}
