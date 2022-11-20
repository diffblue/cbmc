/*******************************************************************\

Module: CPROVER Command Line Option Processing

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Command Line Parsing

#ifndef CPROVER_CPROVER_CPROVER_PARSE_OPTIONS_H
#define CPROVER_CPROVER_CPROVER_PARSE_OPTIONS_H

#define CPROVER_OPTIONS                                                        \
  "(help)?h(version)"                                                          \
  "(smt2)(text)(outfile):"                                                     \
  "(variables)"                                                                \
  "(safety)(no-safety)(no-assertions)"                                         \
  "(contract):"                                                                \
  "(solve)(unwind):(trace)"                                                    \
  "(inline)(no-inline)"                                                        \
  "D:I:"                                                                       \
  "(32)(64)"                                                                   \
  "(show-goto-functions)(show-loops)(show-properties)"                         \
  "(show-functions-with-loops)"                                                \
  "(validate-goto-model)"                                                      \
  "(verbose)"

class cprover_parse_optionst
{
public:
  int main();

  cprover_parse_optionst(int _argc, const char **_argv)
    : argc(_argc), argv(_argv)
  {
  }

protected:
  int argc;
  const char **argv;

  void help();
};

#endif // CPROVER_CPROVER_CPROVER_PARSE_OPTIONS_H
