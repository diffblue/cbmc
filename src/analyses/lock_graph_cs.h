/*******************************************************************\

Module: Lock Graph

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ANALYSES_LOCK_GRAPH_CS_H
#define CPROVER_ANALYSES_LOCK_GRAPH_CS_H

#include "lock_set_analysis_cs.h"

#include <util/multigraph.h>

class lock_graph_cs_edget {
public:
  ai_cs_baset::placet place; 
  lock_graph_cs_edget() {}
  void set(const ai_cs_baset::placet &_place)
  {
    place = _place;
  }
};

class lock_graph_cs_nodet : public multigraph_nodet<lock_graph_cs_edget> {
public:
  typedef value_sett::object_map_dt lock_typet;
  lock_typet lock;
  ai_cs_baset::placest places;

  lock_graph_cs_nodet() {}
  void set(const lock_typet &_lock)
  {
    lock = _lock;
  }
  void add(const ai_cs_baset::placet &_place)
  {
    places.insert(_place);
  }
 
};

class lock_graph_cst : public multigrapht<lock_graph_cs_nodet>
{
public:
  typedef value_sett::object_mapt object_mapt;
  typedef lock_graph_cs_nodet::lock_typet lock_typet;
  void add_lock(const namespacet &ns,
		const lock_typet &locks_held,
		const ai_cs_baset::placet &place,
		const lock_typet &locks_acquired);

  void closure();

  void output(const namespacet &ns, std::ostream &out) const;
  void convert(const namespacet &ns, xmlt &dest);

  static void output_lock(const namespacet &ns, std::ostream &out, 
		   const lock_typet &lock);
  
  bool has_node(const lock_typet &lock, node_indext &n);
  bool has_edge(node_indext n1, node_indext n2,
		const ai_cs_baset::placet &place, edge_indext &e);

  void convert_node(const namespacet &ns, xmlt &dest,
		    node_indext n);
  void convert_edge(const namespacet &ns, xmlt &dest,
		    node_indext n, 
		    node_indext m,
                    edge_indext e);

protected:
  virtual void postprocessing()
  {
    closure();
  }

};

#endif
