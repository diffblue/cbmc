#include "trie.h"

#include <iostream>
#include <list>
#include <cassert>

int main()
{
  trie<unsigned, bool, false> t;
  t[0][1].value = true;
  t[0][2][3].value = true;
  t[0][2][4].value = true;
  t[1].value = true;

  t.output(std::cout);

  trie<unsigned, bool, false> *ptr = &t[0][2][3];
  
  std::list<unsigned> w;
  ptr->build_word(w);
  trie<unsigned, bool, false>::output_word(std::cout, w);

  {
    std::list<unsigned> p;
    p.push_back(0);
    p.push_back(2);

    assert(!t.find(p));
    p.push_back(3);
    assert(t.find(p));
  }

  {
    std::list<unsigned> p;
    p.push_back(0);
    p.push_back(1);
    p.push_back(3);

    assert(t.find_prefix_of(p));
  }

  {
    std::list<unsigned> p;
    p.push_back(2);
    p.push_back(3);

    assert(!t.find_prefix_of(p));

    t.insert(p, true);

    t.output(std::cout);

    assert(t.find(p));
  }

  return 0;
}
