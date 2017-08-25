\ingroup module_hidden
\defgroup module_command-line-parsing Command Line Parsing

\dot
digraph G {
  node [shape=box];
  rankdir="LR";
  1 [shape=none, label=""];
  2 [label="command line parsing"];
  3 [shape=none, label=""];
  1 -> 2 [label="C files or goto-binaries"];
  2 -> 3 [label="Command line options, file names"];
}
\enddot
