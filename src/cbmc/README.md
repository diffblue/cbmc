\ingroup module_hidden
\defgroup cbmc cbmc

# Folder CBMC

\author Martin Brain

This contains the first full application. CBMC is a bounded model
checker that uses the front ends (`ansi-c`, `cpp`, goto-program or
others) to create a goto-program, `goto-symex` to unwind the loops the
given number of times and to produce and equation system and finally
`solvers` to find a counter-example (technically, `goto-symex` is then
used to construct the counter-example trace).
