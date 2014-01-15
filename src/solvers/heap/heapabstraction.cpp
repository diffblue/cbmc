#include "heapabstraction.h"

std::ostream& operator<< (std::ostream& s, const heapabs& sol) {
  s << "Adj list:" << sol.adj_list << std::endl;
  s << "Not eqs:" << sol.not_eqs << std::endl;
  s << "Not paths:" << sol.not_paths << std::endl;
  s << "Sel eqs: ";
  for(sel_eqst::const_iterator it = sol.sel_eqs.begin(); it != sol.sel_eqs.end(); ++it) {
    s << (*it).first << " = " << (*it).second << ";";
  }
  return s;
}

std::ostream& operator<< (std::ostream&, const std::vector< meetIrreduciblep >&); 

