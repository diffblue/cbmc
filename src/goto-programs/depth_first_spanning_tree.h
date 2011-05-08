/*
 * depth_first_spanning_tree.h
 *
 *  Created on: August 18, 2010
 *      Author: Alastair Donaldson
 */

#ifndef DEPTH_FIRST_SPANNING_TREE_H_
#define DEPTH_FIRST_SPANNING_TREE_H_

#include "control_flow_graph.h"

class DFST_numberingt {

public:
	DFST_numberingt(const CFGt& cfg);

	bool is_retreating(const CFG_nodet& d, const CFG_nodet& n) const;

	unsigned int get_number(const CFG_nodet* n) const;

	friend std::ostream& operator<<(std::ostream& os, const DFST_numberingt& dom);

private:

	int search(const CFG_nodet& n, CFGt::nodes_const_sett& visited, int c);

	std::map<const CFG_nodet*, unsigned int> dfn;

	const CFGt& the_cfg;

};

#endif
