#include "heapabstraction.h"

// std::ostream& operator<< (std::ostream& s, const solutiont& contents) {
//    s << "{";

//    for(solutiont::const_iterator it = contents.begin(); it!= contents.end(); ++it) {
//      s << *it << ";";
//    }

//    s << "}";

//   return s;
//  }


// std::ostream& operator<< (std::ostream& s, const heapabs& h) {
//   s << h.contents;
//    // s << "{";

//    // for(solutiont::const_iterator it = h.contents.begin(); it!= h.contents.end(); ++it) {
//    //   s << *it << ";";
//    // }

//    // s << "}";
//    return s;
//  }

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

// bool subseteq(solutiont& subset, solutiont& set, bool& gamma) {
//     for(solutiont::const_iterator it = subset.begin(); it != subset.end(); ++it) {
//       //std::cout << "subseteq check for " << **it << std::endl;
//       if(set.find(*it) == set.end()) {
// 	(*it)->flip_state();
// 	if(set.find(*it) == set.end()) {
// 	  //std::cout << "[hcp] missing information about: " << (*it) << std::endl;	  
// 	  gamma = false;
// 	}
// 	//std::cout << "not found" << std::endl;
// 	return false;
//       }
//     }
//     return true;
//   }

/*
std::ostream& operator<< (std::ostream& s, const trailt& t) {
  for (trailt::const_iterator it = t.begin(); it != t.end(); ++it) {
    s << (*it)->inference->lit << " ";
  }
  return s;
}
*/
