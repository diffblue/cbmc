#include <iostream>

#include "heapliteral.h"

domaint mode;

std::ostream& operator<< (std::ostream& s, const heapvar& v) {
  s << v.name;
  return s;
}

std::ostream& operator << (std::ostream& s, const std::set<heapvar>& v) {
  
  for(std::set<heapvar>::const_iterator it = v.begin(); it != v.end(); ++it) {
    s << *it << " ";
  }

  return s;
}

std::ostream& operator << (std::ostream& s, const std::vector<heapvar>& v) {
  
  for(std::vector<heapvar>::const_iterator it = v.begin(); it != v.end(); ++it) {
    s << *it << " ";
  }

  return s;
}


std::ostream& operator << (std::ostream& s, const ssa_countst& v) {
  for(ssa_countst::const_iterator it = v.begin(); it != v.end(); ++it) {
    s << (*it).first << "= " << (*it).second << ";";
  }
  s << std::endl;
  return s;
}

std::ostream& operator<< (std::ostream& s, const heapexpr& e) {  
    if (e.is_nil())
      s << "NULL";
    else
    if (e.is_var())
      s << e.v;
    else
    s << "sel(" << e.m << "," << e.v << "," << e.f << ")";

    return s;
}

std::ostream& operator<< (std::ostream& s, const meetIrreducible& l) {
  s << l.lit;
  return s;
}

std::ostream& operator<< (std::ostream& s, const meetIrreduciblep& l) {
  s << l->lit;
  return s;
}

std::ostream& operator<< (std::ostream& s, const std::vector<meetIrreduciblep>& v) {

  for (std::vector<meetIrreduciblep>::const_iterator it = v.begin(); it != v.end(); ++it) {
    s << *it << " ";
  }

  return s;
}

std::ostream& operator<< (std::ostream& s, const solutiont& v) {

  for(std::set<meetIrreduciblep>::const_iterator it = v.begin(); it != v.end(); ++it) {
    s << *it << " ";
  }

  return s;
}

std::ostream& operator<< (std::ostream& s, const hintt& v) {

  for(std::set< std::pair<meetIrreduciblep, hintPriority::s> >::const_iterator it = v.begin(); it != v.end(); ++it) {
    s << (*it).first << " ";
  }

  return s;
}


std::ostream& operator<< (std::ostream& s, const trailt& v) {

  for(trailt::const_iterator it = v.begin(); it != v.end(); ++it) {
    s << (*it)->inference << " ";
  }

  return s;
}


meetIrreduciblep copy_lit(const meetIrreduciblep& l) {
  meetIrreduciblep hl;

  switch ((l->lit)->type) {
  case PATH: {
    hl = new meetIrreducible(new path_lit(*(l->lit)));
    return hl;
  }
  case ONPATH: {
    hl = new meetIrreducible(new onpath_lit(*(l->lit)));
    return hl;
  }
  case DANGLING: {
    hl = new meetIrreducible(new dangling_lit(*(l->lit)));
    return hl;
  }
  case DISJ: {
    hl = new meetIrreducible(new disj_lit(*(l->lit)));
    return hl;
  }
  case EQ:{
    hl = new meetIrreducible(new eq_lit(*(l->lit)));
    return hl; 
  }
  // default: {  
  //   hl = new meetIrreducible(new heapelem(*(l->lit)));
  //   return hl;
  // }
  default: 
    assert(1 == 0);
    return new meetIrreducible(new heapelem(*(l->lit)));
}

}


meetIrreduciblep copy_lit(const heaplit& lit) {
  meetIrreduciblep hl;

  switch (lit.type) {
  case PATH: {
    hl = new meetIrreducible(new path_lit(lit));
    return hl;
  }
  case ONPATH: {
    hl = new meetIrreducible(new onpath_lit(lit));
    return hl;
  }
  case DANGLING: {
    hl = new meetIrreducible(new dangling_lit(lit));
    return hl;
  }
  case DISJ: {
    hl = new meetIrreducible(new disj_lit(lit));
    return hl;
  }
  case EQ:{
    hl = new meetIrreducible(new eq_lit(lit));
    return hl; 
  }
  default: 
    debugc("[copy_lit]: unhandled literal " << lit, 1);
    debugc("[copy_lit]: unhandled literal type " << lit.type, 1);
    assert(1 == 0);
    return new meetIrreducible(new heapelem(lit));
    
  // {  
  //   hl = new meetIrreducible(new heapelem(lit));
  //   return hl;
  // }
  }
}

heaplit* copy_lit(heaplit* lit) {
  switch (lit->type) {
  case PATH: return new path_lit(*lit);
  case ONPATH: return new onpath_lit(*lit);
  case DANGLING: return new dangling_lit(*lit);
  case DISJ: return new disj_lit(*lit);
  case EQ: return new eq_lit(*lit);
  case NEW: return new new_lit(*lit);
  case FREE: return new free_lit(*lit);
  case STORE: return new store_lit(*lit);
  default: 
    assert(false);
  }
}

std::ostream& operator<< (std::ostream& s, const clauset& f) {
  s << "(";

  for(unsigned int i = 0; i < (f.size()-1); ++i) {
     s << f[i] << " or ";
  }

  if(f.size() > 0)
    s << f[f.size()-1];


  s << ")";
  return s;
}

// std::ostream& operator<< (std::ostream& s, const std::set< heapvar >& f) {
//   for(std::set< heapvar >::const_iterator it = f.begin(); it != f.end(); ++it) {
//     s << it->name << " ";
//   }
//   s << std::endl;
// } 

std::ostream& operator<< (std::ostream& s, const formulat& f) {

  if(f.size() > 0) {
    for(unsigned int i = 0; i < (f.size()-1); ++i) {
      s << *(f[i]) << " and ";
    }
  }

  if(f.size() > 0)
    s << *(f[f.size()-1]);

  s << std::endl;
  return s;
}


// std::ostream& operator<< (std::ostream& s, const solutiont& sol) {
//    s << "{";

//    for(solutiont::const_iterator it = sol.begin(); it!= sol.end(); ++it) {
//      s << *it << ";";
//    }

//    s << "}";
//    return s;
//  }


// std::ostream& operator<< (std::ostream& s, const equiv_sett& es) {
//   for(equiv_sett::const_iterator it = es.begin(); it != es.end(); ++it) {
//     s << *it << "; ";
//   }

//   return s;
// }

// std::ostream& operator<< (std::ostream& s, const equiv_setst& es) {

//   for(equiv_setst::const_iterator it = es.begin(); it != es.end(); ++it) {
//     s << *it << std::endl;
//   }

//   return s;
// }


std::ostream& operator<< (std::ostream& s, const not_eqst& sne) {

  for(not_eqst::const_iterator it = sne.begin(); it != sne.end(); ++it) {
    s << (*it).first << " != " << (*it).second << ";";
  }
  
  s << std::endl;
  return s;
} 

std::ostream& operator<< (std::ostream& s, const not_eqt& sne) {

    s << sne.first << " != " << sne.second << ";";
  
  return s;
} 


std::ostream& operator<< (std::ostream& s, const fld_adj_listt& m) {

  for(fld_adj_listt::const_iterator it = m.begin(); it != m.end(); ++it) {
    s << (*it).first << "-> {"  << (*it).second << "}";
  }

  return s;
}

std::ostream& operator<< (std::ostream& s, const mem_adj_listt& m) {

  for(mem_adj_listt::const_iterator it = m.begin(); it != m.end(); ++it) {
    s << "fld " << (*it).first << ": " << (*it).second;
  }

  return s;
}

std::ostream& operator<< (std::ostream& s, const adj_listt& m) {

  for(adj_listt::const_iterator it = m.begin(); it != m.end(); ++it) {
    s << "mem " << (*it).first << ": "  << (*it).second;
  }

  return s;
}

std::ostream& operator<< (std::ostream& s, const not_pathst& np) {
  for(not_pathst::const_iterator it = np.begin(); it != np.end(); ++it)
    s << "!Path(" << (*it)->m << ", " << (*it)->x << ", " << (*it)->y << ", " << (*it)->f << ") " ;
  
  return s;
}
