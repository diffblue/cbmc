/*******************************************************************\

Module: A minimalistic BDD library, following Bryant's original paper
        and Andersen's lecture notes

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// A minimalistic BDD library, following Bryant's original paper and Andersen's
///   lecture notes

#include "miniBDD.h"

#include <iostream>

int main()
{
  mini_bdd_mgrt mgr;
  mini_bddt result;

#if 0
  {
    auto x=mgr.Var("x");
    auto y=mgr.Var("y");
    auto z=mgr.Var("z");
    result=x | (y &z);
  }
#elif 0
  {
    auto y = mgr.Var("y");
    auto x = mgr.Var("x");
    auto z = mgr.Var("z");
    result = x | (y & z);
  }
#elif 0
  {
    auto x1 = mgr.Var("x_1");
    auto x2 = mgr.Var("x_2");
    auto x3 = mgr.Var("x_3");
    auto x4 = mgr.Var("x_4");
    result = (x1 & x2) | (x3 & x4);
  }
#elif 0
  {
    auto x1 = mgr.Var("x_1");
    auto x2 = mgr.Var("x_2");
    auto x3 = mgr.Var("x_3");
    auto x4 = mgr.Var("x_4");
    auto tmp = (x1 & x2) | (x3 & x4);
    result = restrict(tmp, x2.var(), 0);
  }
#else
  {
    auto a = mgr.Var("a");
    auto b = mgr.Var("b");
    auto f = (!a) | b;
    auto fp = !b;
    result = f == fp;
  }
#endif

  mgr.DumpTikZ(std::cout);
}
