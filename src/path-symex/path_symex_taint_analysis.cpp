/*******************************************************************
 Module: Taint Engine Module

 Author: Daniel Neville,	daniel.neville@cs.ox.ac.uk
 John Galea,		john.galea@cs.ox.ac.uk

 \*******************************************************************/

#include "path_symex_taint_analysis.h"

// Returns the maximal/top element of the lattice.
const taintt path_symex_taint_analysis_enginet::get_top_elem()
{
  return 0;
}

const taintt path_symex_no_taint_analysis_enginet::get_bottom_elem() const
{
  return 0;
}

taintt path_symex_no_taint_analysis_enginet::meet(irep_idt id, taintt taint_1,
    taintt taint_2) const
{
  return 0;
}

const std::string path_symex_no_taint_analysis_enginet::get_taint_analysis_name() const
{
  return "None";
}

taintt path_symex_no_taint_analysis_enginet::parse_taint(
    std::string taint_name) const
{
  return 0;
}

std::string path_symex_no_taint_analysis_enginet::get_taint_name(
    taintt taint) const
{
  return "";
}

const taintt path_symex_simple_taint_analysis_enginet::get_bottom_elem() const
{
  return TAINTED;
}

taintt path_symex_simple_taint_analysis_enginet::meet(irep_idt id,
    taintt taint1, taintt taint2) const
{
  // Perform checks on passed taint types.
  if(taint1 != UNTAINTED && taint1 != TAINTED)
  {
    throw "First taint type  passed to meet function is invalid.";
  }

  if(taint2 != UNTAINTED && taint2 != TAINTED)
  {
    throw "Second taint type passed to meet function is invalid.";
  }

  // If either taint state is tainted, then the result is tainted.
  return (taint1 == TAINTED || taint2 == TAINTED) ? TAINTED : UNTAINTED;
}

const std::string path_symex_simple_taint_analysis_enginet::get_taint_analysis_name() const
{
  return "Simple taint domain.";
}

taintt path_symex_simple_taint_analysis_enginet::parse_taint(
    std::string taint_name) const
{
  /* Parse from strings -> taint types */
  if(taint_name == "untainted")
    return UNTAINTED;
  if(taint_name == "tainted")
    return TAINTED;
  throw "Taint type not recognised";
}

std::string path_symex_simple_taint_analysis_enginet::get_taint_name(
    taintt taint) const
{
  /* Parse from taint -> strings types */
  switch (taint)
  {
    case UNTAINTED:
      return "untainted";
    case TAINTED:
      return "tainted";
  }
  throw "Taint type not recognised";
}
