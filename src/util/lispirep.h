/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

class irept;
class lispexprt;

void lisp2irep(const lispexprt &src, irept &dest);
void irep2lisp(const irept &src, lispexprt &dest);
