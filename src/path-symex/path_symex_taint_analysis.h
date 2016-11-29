/*******************************************************************
 Module: Taint Engine Module

 We define taint lattices to represent taint types (the domain).
 In order to implement analysis using a new taint domain, one
 needs to implement the path_symex_taint_analysis_enginet
 interface.

 Author: Daniel Neville,	daniel.neville@cs.ox.ac.uk
 John Galea,				john.galea@cs.ox.ac.uk

 \*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_TAINT_ANALYSIS_H
#define CPROVER_PATH_SYMEX_TAINT_ANALYSIS_H

#include <util/std_expr.h>
#include "locs.h"
#include <string>

/* Future work.
 *
 * Consider whether a goto_check for printf not-tainted should be inserted
 * (but under what taint engine?)
 *
 * Make taint JSON file syntactically 'similar' to A.I. taint file.
 *
 * Consider tainting function calls under some semantics.
 */

// We represent positions in a taint lattice as unsigned short value.
typedef unsigned short taintt;

class taint_datat;

/**
 * 	Interface for taint analysis, which differ in their considered domains.
 */
class path_symex_taint_analysis_enginet
{

public:

  inline virtual ~path_symex_taint_analysis_enginet()
  {
  }

  // Returns the maximal/top element of the lattice.
  const static taintt get_top_elem();

  // Returns the minimal/lowest element of the lattice.
  virtual const taintt get_bottom_elem() const = 0;

  // Given two taint types, the meet of the two is returned.
  virtual taintt meet(irep_idt id, const taintt taint_1,
      const taintt taint_2) const = 0;

  // Returns the name of the taint analysis engine
  virtual const std::string get_taint_analysis_name() const = 0;

  // Returns the taint type corresponding to the string
  virtual taintt parse_taint(const std::string taint_name) const = 0;

  // Returns the name of a given taint type
  virtual std::string get_taint_name(const taintt taint) const = 0;

  // Taint Data.
  taint_datat *taint_data;

  // A flag specifying whether the taint engine is to be used.
  bool enabled=false;
};

typedef path_symex_taint_analysis_enginet taint_enginet;

class path_symex_no_taint_analysis_enginet: public taint_enginet
{

// A dummy implementation of a taint engine that performs no taint analysis.
public:

  inline ~path_symex_no_taint_analysis_enginet()
  {
  }

  const taintt get_bottom_elem() const;

  taintt meet(irep_idt id, const taintt taint_1, const taintt taint_2) const;

  const std::string get_taint_analysis_name() const;

  taintt parse_taint(const std::string taint_name) const;

  std::string get_taint_name(const taintt taint) const;

};

/*
 *  An implementation of a simple taint engine with two states (tainted
 *	and untainted).
 */
class path_symex_simple_taint_analysis_enginet: public taint_enginet
{
public:
  static const taintt UNTAINTED=0;
  static const taintt TAINTED=1;

  inline ~path_symex_simple_taint_analysis_enginet()
  {
  }

  const taintt get_bottom_elem() const;

  taintt meet(irep_idt id, const taintt taint_1, const taintt taint_2) const;

  const std::string get_taint_analysis_name() const;

  taintt parse_taint(const std::string taint_name) const;

  std::string get_taint_name(const taintt taint) const;
};

#endif
