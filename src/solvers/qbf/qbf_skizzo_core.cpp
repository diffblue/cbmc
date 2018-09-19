/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/

#include <fstream>

#include <util/invariant.h>

#include <util/string2int.h>

#include <cuddObj.hh> // CUDD Library

/*! \cond */
// FIX FOR THE CUDD LIBRARY

inline DdNode *DD::getNode() const
{
    return node;
} // DD::getNode
/*! \endcond */

#include <dddmp.h>

#include "qbf_skizzo_core.h"

qbf_skizzo_coret::qbf_skizzo_coret():
  qbf_bdd_certificatet()
{
  // skizzo crashes on broken lines
  break_lines=false;
  qbf_tmp_file="sKizzo.qdimacs";
}

qbf_skizzo_coret::~qbf_skizzo_coret()
{
}

const std::string qbf_skizzo_coret::solver_text()
{
  return "Skizzo/Core";
}

propt::resultt qbf_skizzo_coret::prop_solve()
{
  // sKizzo crashes on empty instances
  if(no_clauses()==0)
    return P_SATISFIABLE;

  {
    std::string msg=
      "Skizzo: "+
      std::to_string(no_variables())+" variables, "+
      std::to_string(no_clauses())+" clauses";
    messaget::status() << msg << messaget::eom;
  }

  std::string result_tmp_file="sKizzo.out";

  {
    std::ofstream out(qbf_tmp_file.c_str());

    // write it
    break_lines=false;
    write_qdimacs_cnf(out);
  }

  std::string options="";

  // solve it
  system((
    "sKizzo -log "+qbf_tmp_file+options+" > "+result_tmp_file).c_str());

  bool result=false;

  // read result
  {
    std::ifstream in(result_tmp_file.c_str());

    bool result_found=false;
    while(in)
    {
      std::string line;

      std::getline(in, line);

      if(line!="" && line[line.size()-1]=='\r')
        line.resize(line.size()-1);

      if(line=="The instance evaluates to TRUE.")
      {
        result=true;
        result_found=true;
        break;
      }
      else if(line=="The instance evaluates to FALSE.")
      {
        result=false;
        result_found=true;
        break;
      }
    }

    if(!result_found)
    {
      messaget::error() << "Skizzo failed: unknown result" << messaget::eom;
      return P_ERROR;
    }
  }

  remove(result_tmp_file.c_str());
  remove(qbf_tmp_file.c_str());

  if(result)
  {
    messaget::status() << "Skizzo: TRUE" << messaget::eom;

    if(get_certificate())
      return P_ERROR;

    return P_SATISFIABLE;
  }
  else
  {
    messaget::status() << "Skizzo: FALSE" << messaget::eom;
    return P_UNSATISFIABLE;
  }
}

bool qbf_skizzo_coret::is_in_core(literalt l) const
{
  UNIMPLEMENTED;
}

qdimacs_coret::modeltypet qbf_skizzo_coret::m_get(literalt a) const
{
  UNIMPLEMENTED;
}

bool qbf_skizzo_coret::get_certificate(void)
{
  std::string result_tmp_file="ozziKs.out";
  std::string options="-dump qbm=bdd";
  std::string log_file=qbf_tmp_file+".sKizzo.log";

  system((
    "ozziKs "+options+" "+log_file+" > "+result_tmp_file).c_str());

  // read result
  bool result=false;
  {
    std::ifstream in(result_tmp_file.c_str());
    std::string key="  [OK, VALID,";

    while(in)
    {
      std::string line;

      std::getline(in, line);

      if(line!="" && line[line.size()-1]=='\r')
        line.resize(line.size()-1);

      if(line.compare(0, key.size(), key)==0)
      {
        result=true;
        break;
      }
    }
  }

  if(!result)
  {
    messaget::error() << "Skizzo failed: unknown result" << messaget::eom;
    return true;
  }

  remove(result_tmp_file.c_str());
  remove(log_file.c_str());

  // certificate reconstruction done, now let's load it from the .qbm file

  int n_e;
  std::vector<int> e_list;
  int e_max=0;

  // check header
  result=false;
  {
    std::ifstream in((qbf_tmp_file+".qbm").c_str());
    std::string key="# existentials[";

    std::string line;
    std::getline(in, line);

    INVARIANT_WITH_DIAGNOSTICS(
      line == "# QBM file, 1.3",
      "QBM file has to start with this exact string: ",
      "# QBM file, 1.3");

    while(in)
    {
      std::getline(in, line);

      if(line!="" && line[line.size()-1]=='\r')
        line.resize(line.size()-1);

      if(line.compare(0, key.size(), key)==0)
      {
        result=true;
        break;
      }
    }

    size_t ob=line.find('[');
    std::string n_es=line.substr(ob+1, line.find(']')-ob-1);
    n_e=unsafe_string2int(n_es);
    INVARIANT(n_e != 0, "there has to be at least one existential variable");

    e_list.resize(n_e);
    std::string e_lists=line.substr(line.find(':')+2);

    for(int i=0; i<n_e; i++)
    {
      size_t space=e_lists.find(' ');

      int cur=unsafe_string2int(e_lists.substr(0, space));
      INVARIANT(cur != 0, "variable numbering starts with 1");

      e_list[i]=cur;
      if(cur>e_max)
        e_max=cur;

      e_lists=e_lists.substr(space+1);
    }

    INVARIANT(result, "existential mapping from sKizzo missing");

    in.close();

    // workaround for long comments
    system((
      "sed -e \"s/^#.*$/# no comment/\" -i "+qbf_tmp_file+".qbm").c_str());
  }


  {
    DdNode **bdds;
    std::string bdd_file=qbf_tmp_file+".qbm";

    // dddmp insists on a non-const string here...
    // The linter insists on compile time constant for arrays
    char filename[bdd_file.size()+1]; // NOLINT(*)
    snprintf(filename, bdd_file.size()+1, bdd_file.c_str());

    bdd_manager->AutodynEnable(CUDD_REORDER_SIFT);

    int nroots=
      Dddmp_cuddBddArrayLoad(
        bdd_manager->getManager(),
        DDDMP_ROOT_MATCHLIST,
        NULL,
        DDDMP_VAR_MATCHIDS,
        NULL,
        NULL,
        NULL,
        DDDMP_MODE_DEFAULT,
        filename,
        NULL,
        &bdds);

    INVARIANT(
      nroots == 2 * n_e,
      "valid QBM certificate should have twice as much roots as the "
      "existential variables");

    model_bdds.resize(e_max+1, NULL);

    for(unsigned i=0; i<e_list.size(); i++)
    {
      int cur=e_list[i];
      DdNode *posNode=bdds[2*i];
      DdNode *negNode=bdds[2*i+1];

      if(Cudd_DagSize(posNode)<=Cudd_DagSize(negNode))
        model_bdds[cur]=new BDD(*bdd_manager, posNode);
      else
        model_bdds[cur]=new BDD(*bdd_manager, Cudd_Not(negNode));
    }

    // tell CUDD that we don't need those BDDs anymore.
    for(int i=0; i<nroots; i++)
      Cudd_Deref(bdds[i]);

    free(bdds);
    bdds=NULL;
    remove(bdd_file.c_str());
    remove((qbf_tmp_file+".qbm").c_str());
  }


  return false;
}
