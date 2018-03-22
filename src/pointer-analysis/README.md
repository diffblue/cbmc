\ingroup module_hidden
\defgroup pointer-analysis pointer-analysis

# Folder pointer-analysis

\author Martin Brain

To perform symbolic execution on programs with dereferencing of
arbitrary pointers, some alias analysis is needed.  `pointer-analysis`
contains the three levels of analysis; flow and context insensitive,
context sensitive and flow and context sensitive. The code needed is
subtle and sophisticated and thus there may be bugs.
