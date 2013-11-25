#include <vector>
#include <algorithm>

class groupt:protected std::vector<unsigned>
{
 protected:
  typedef std::vector<unsigned> baset;

 public:
  unsigned rep(unsigned a)
  {
    return (*this)[a];
  }
 
  void merge(unsigned a, unsigned b)
  {
    unsigned rep_a=rep(a),
             rep_b=rep(b);
             
    unsigned new_rep=std::min(rep_a, rep_b);
    
    (*this)[a]=new_rep;
    (*this)[b]=new_rep;
    
    if(rep_a!=a || rep_b!=b)
      for(unsigned i=0; i<size(); i++)
        if(rep(i)==rep_a ||
           rep(i)==rep_b)
          (*this)[i]=new_rep;
  }
 
  void init(unsigned s)
  {
    resize(s);
    for(unsigned i=0; i<s; i++)
      (*this)[i]=i;
  }
   
  baset::size_type size() { return baset::size(); }
};

