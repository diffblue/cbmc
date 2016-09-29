/*******************************************************************
 Module: Taint Data Module

 Author: Daniel Neville,	daniel.neville@cs.ox.ac.uk
 John Galea,		john.galea@cs.ox.ac.uk

 \*******************************************************************/

#ifndef PATH_SYMEX_PATH_SYMEX_TAINT_DATA_H_
#define PATH_SYMEX_PATH_SYMEX_TAINT_DATA_H_

#include <path-symex/path_symex_taint_analysis.h>
#include <map>
#include <util/std_expr.h>

class taint_datat
{
public:

  // Defines a taint rule.
  class taint_rulet
  {
  public:
    // The location where taint is forced.  (Redundant.)
    unsigned int loc;

    // The taint state the force.
    taintt taint;

    // Modify a symbol, or just the LHS?
    bool symbol_flag;

    // The name of the symbol to be updated.
    irep_idt symbol_name;

    // Output a rule using the taint engine.
    void output(taint_enginet &taint_engine, std::ostream &out) const;
    // Defaults
    taint_rulet();
  };

  taint_datat();

  typedef std::map<unsigned, std::vector<taint_rulet> > datat;
  datat data;

  void add(unsigned loc, taintt taint, bool symbol_flag, irep_idt symbol_name);

  bool check_rules(locst &locs, std::ostream & warning,
      taint_enginet &taint_engine);

  void output(std::ostream &out, taint_enginet &taint_engine) const;

};

#endif /* PATH_SYMEX_PATH_SYMEX_TAINT_DATA_H_ */
