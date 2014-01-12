//#include "heaputil.h"
#ifndef HEAPWATCHES
#define HEAPWATCHES

#include "heapabstraction.h"

class heapwatches {
 public:
  watcht w;
  trailt::const_iterator trail_it;


  // add a pair (lit, wl) to the watch
  void add_literal_to_watch(const heaplitp lit, watchlist* wl) {

    for(watcht::const_iterator it = w.begin(); it != w.end(); ++it) {
      debugc("[add_literal_to_watch]: before loop found literal " << *lit << " and " << *((*it).first), 0);
      if (*((*it).first) == *lit) {
	debugc("[add_literal_to_watch]: equal literals " << *lit, 0);
  	(*it).second->insert((*it).second->begin(), wl->begin(), wl->end());
  	return;
      }
    }
    w.push_back(std::make_pair(lit, wl));
  }

  void init_watch(formulat& f) {
    for(formulat::const_iterator clause_it = f.begin(); clause_it != f.end(); ++clause_it)
      for(clauset::const_iterator lit_it = (*clause_it)->begin(); lit_it != (*clause_it)->end(); ++lit_it) {
	watchlist* new_wl = new watchlist;
	debugc("[init_watch]: adding literal " << *lit_it << " with wlist size " << new_wl->size(), 0);
  	add_literal_to_watch(*lit_it, new_wl);
      }
  }


bool vars_overlap(std::set<heapvar> set1, std::set<heapvar> set2) {
  for(std::set<heapvar>::const_iterator it = set1.begin(); it != set1.end(); ++it)
    if (set2.find(*it) != set2.end())
      return true;
  return false;
}

std::set<heapvar> get_vars_from_clause(clauset* c) {
  std::set<heapvar> ret;

  for(clauset::const_iterator it = c->begin(); it != c->end(); ++it) {
    std::set<heapvar> lit_vars = (*it)->get_vars();
    ret.insert(lit_vars.begin(), lit_vars.end());
  }

  return ret;
}


  void add_clause_to_watch(clauset* c) {
    
    std::set<heapvar> clause_vars = get_vars_from_clause(c);

    for(watcht::const_iterator it = w.begin(); it != w.end(); ++it) {
      std::set<heapvar> lit_vars = (it->first)->get_vars();
      if (vars_overlap(lit_vars, clause_vars)) {
	(*it).second->push_back(c);
      }
    }

    /* watchlist* wl = new watchlist(); */
    /* wl->push_back(c); */
    /* watch.push_back(std::make_pair(lit, wl)); */
  }


  /* void add_clause_to_watch(const heapvar v, clauset* c) { */

  /*   for(watcht::const_iterator it = watch.begin(); it != watch.end(); ++it) { */
  /*     if (*((*it).first) == *lit) { */
  /* 	(*it).second->push_back(c); */
  /* 	return; */
  /*     } */
  /*   } */
  /*   watchlist* wl = new watchlist(); */
  /*   wl->push_back(c); */
  /*   watch.push_back(std::make_pair(lit, wl)); */
  /* } */





  /* bool done_watching(trailt trail) { */
  /*   return trail_it == trail.end();  */
  /* } */

  /* watchlist* get_next_watch_list(trailt trail) { */
  /*   watchlist* nextwl; */
    
  /*   assert(trail_it != trail.end()); */

  /*   heaplitp current_lit = trail_it->inference->lit; */

  /*   for(watcht::const_iterator it = watch.begin(); it != watch.end(); ++it) { */
  /*     if (*(it->first) == *current_lit) { */
  /* 	++trail_it; */
  /* 	return it->second; */
  /*     } */
  /*   } */

  /*   assert(0); */
  /*   return NULL; */
  /* } */


};

inline std::ostream& operator<< (std::ostream& s, const heapwatches& watch) {

     for(watcht::const_iterator it = watch.w.begin(); it != watch.w.end(); ++it) {
       s << "literal " << it->first << " is watching:";
       watchlist* wl = it->second;
       //s << " size " << wl->size();
       for(watchlist::const_iterator lit_it = wl->begin();  lit_it != wl->end(); ++lit_it) {
       	 s << *lit_it << "; ";
       }
     }

     s << std::endl;
     return s;
}


#endif
