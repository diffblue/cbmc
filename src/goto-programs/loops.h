/*
 * loops.h
 *
 *  Created on: August 18, 2010
 *      Author: Alastair Donaldson
 */

#ifndef LOOPS_H_
#define LOOPS_H_

#include "dominator_info.h"
#include "induction_variable.h"

class loop_infot /* Represents a nest of loops */
{
public:

	/* Uses Dragon book algorithm to compute all natural loops for goto program */
	loop_infot(const CFGt&);

	/* Returns number of loops in the nest */
	unsigned int num_loops() const;

	/* Display information about the loop nest */
	friend std::ostream& operator<<(std::ostream& os, const loop_infot& loop_info);

	class loopt;
	typedef std::vector<loopt*> loopst;
	typedef std::vector<const loopt*> const_loopst;

	class loopt /* Represents a single loop */
	{
	public:

		loopt(const CFG_nodet* header, CFGt::nodes_const_sett nodes, const CFGt* cfg);

		void add_nodes(CFGt::nodes_const_sett nodes);

		bool contains( const loopt& other) const;

		bool contains( const CFG_nodet& inst) const;

		static bool disjoint ( loopt& loop1, loopt& loop2 );

		void candidate_parent( loopt& other );

		friend std::ostream& operator<<(std::ostream& os, const loopt& loop);

		loopt* parent; // Pointer to loop containing this one

		loopst children; // Inner loops

		const CFG_nodet* header;

		const CFGt* cfg;

		void find_simple_induction_variables(std::set<induction_variablet>& result);

		unsigned int num_nodes() const;

		void calculate_post_nodes(std::vector<const CFG_nodet*>& result) const;

		CFGt::nodes_const_sett::const_iterator begin() const
		{
			return nodes.begin();
		}

		CFGt::nodes_const_sett::const_iterator end() const
		{
			return nodes.end();
		}

		unsigned depth() const
		{
		  return parent == NULL ? 0 : 1 + parent->depth();
		}

	private:

		bool on_critical_path(const CFG_nodet& n) const;

		bool is_new_post_node(std::vector<const CFG_nodet*>& post_nodes, CFG_nodet* n) const;

		CFGt::nodes_const_sett nodes;

		unsigned id;

	};

	bool is_inner_loop(const loopt* loop) const;

	std::list<loopt> loops; /* All loops */

 	loopst outer_loops; /* Just the outer loops */

	loopst inner_loops; /* Just the inner loops */

	loopt* get_closest_containing_loop(const CFG_nodet* n) const;  /* Returns the innermost loop that contains the given node, returns NULL if the node is not in any loop */

	loopt* get_largest_containing_loop(const CFG_nodet* n) const; /* Returns the outermost loop that contains the given node, returns NULL if the node is not in any loop */

private:

	void compute_loop_nodes_for_back_edge(const CFG_nodet& n,
			const CFG_nodet& d,
			CFGt::nodes_const_sett & loop);

	/* Organizes loops into containment chains, and associates each instruction with the inner-most loop that contains it */
	void organize_loops(const CFGt& cfg);

	std::map<const CFG_nodet*, loopt*> closest_containing_loop;

};

#endif
