/*
 * dominator_info.h
 *
 *  Created on: August 18, 2010
 *      Author: Alastair Donaldson
 */

#ifndef DOMINATOR_INFO_H_
#define DOMINATOR_INFO_H_

#include "control_flow_graph.h"
#include "depth_first_spanning_tree.h"

class dominator_infot {

public:
	dominator_infot(const CFGt& cfg);

	bool dominates(const CFG_nodet& first, const CFG_nodet& second) const;

	/* Determines whether instruction source dominates instruction dest */
	bool is_back_edge(const CFG_nodet& source, const CFG_nodet& dest) const;

	/* Determines whether the CFG is reducible */
	bool cfg_is_reducible(const DFST_numberingt& dfst);

	friend std::ostream& operator<<(std::ostream& os, const dominator_infot& dom);

private:

	typedef std::map<const CFG_nodet*, CFGt::nodes_const_sett > dominator_mapt;

	/* dominators_of[n] is all the nodes that dominate n.  See page 670 of Dragon Book, first edition */
	dominator_mapt dominators_of;

	const CFGt& the_cfg;

};

#endif
