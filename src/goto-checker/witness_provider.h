/*******************************************************************\

Module: Interface for outputting GraphML Witnesses for Goto Checkers

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Interface for outputting GraphML Witnesses for Goto Checkers

#ifndef CPROVER_GOTO_CHECKER_WITNESS_PROVIDER_H
#define CPROVER_GOTO_CHECKER_WITNESS_PROVIDER_H

class goto_tracet;

/// An implementation of `incremental_goto_checkert`
/// may implement this interface to provide GraphML witnesses.
class witness_providert
{
public:
  virtual ~witness_providert() = default;

  // Outputs an error witness in GraphML format (see `graphml_witnesst`)
  virtual void output_error_witness(const goto_tracet &) = 0;

  // Outputs a proof in GraphML format (see `graphml_witnesst`)
  virtual void output_proof() = 0;
};

#endif // CPROVER_GOTO_CHECKER_WITNESS_PROVIDER_H
