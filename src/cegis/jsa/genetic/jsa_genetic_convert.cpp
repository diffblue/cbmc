/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/jsa/converters/solution.h>
#include <cegis/jsa/learn/jsa_symex_learn.h>
#include <cegis/jsa/genetic/jsa_genetic_convert.h>

jsa_genetic_convertt::jsa_genetic_convertt(const jsa_symex_learnt &learn) :
    learn(learn)
{
}

void jsa_genetic_convertt::convert(candidatet &candidate,
    const individualt &individual) const
{
  candidate=::convert(individual, learn.get_jsa_program());
}

void jsa_genetic_convertt::show(messaget::mstreamt &os,
    const candidatet &candidate) const
{
  learn.show_candidate(os, candidate);
}
