/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "union_find.h"

#include <algorithm>

void unsigned_union_find::make_union(size_type j, size_type k)
{
  check_index(j);
  check_index(k);

  // make sure j, k are roots
  j=find(j);
  k=find(k);

  if(j==k)
    return; // already in same set

  // weight it

  if(nodes[j].count < nodes[k].count)  // j is the smaller set
  {
    nodes[k].count+=nodes[j].count;  // so k becomes parent to j
    nodes[j].parent=k;
    nodes[j].count=0;
  }
  else // j is NOT the smaller
  {
    nodes[j].count+=nodes[k].count;  // so j becomes parent to k
    nodes[k].parent=j;
    nodes[k].count=0;
  }
}

void unsigned_union_find::isolate(size_type a)
{
  check_index(a);

  // is a itself a root?
  if(is_root(a))
  {
    size_type c=nodes[a].count;
    DATA_INVARIANT(c != 0, "a root cannot have a node count of zero");

    // already isolated?
    if(c==1)
      return;

    // find a new root
    size_type new_root=get_other(a);
    CHECK_RETURN(new_root != a);

    re_root(a, new_root);
  }

  // now it's not a root
  // get its root
  size_type r=find(a);

  nodes[r].count--;
  nodes[a].parent=a;
  nodes[a].count=1;
}

void unsigned_union_find::re_root(size_type old_root, size_type new_root)
{
  check_index(old_root);
  check_index(new_root);

  // make sure old_root is a root
  old_root=find(old_root);

  // same set?
  if(find(new_root)!=old_root)
    return;

  PRECONDITION(!is_root(new_root));
  PRECONDITION(nodes[old_root].count >= 2);

  nodes[new_root].parent=new_root;
  nodes[new_root].count=nodes[old_root].count;

  nodes[old_root].parent=new_root;
  nodes[old_root].count=0;

  // the order here is important!

  for(size_type i=0; i<size(); i++)
    if(i!=new_root && i!=old_root && !is_root(i))
    {
      size_type r=find(i);
      if(r==old_root || r==new_root)
        nodes[i].parent=new_root;
    }
}

unsigned_union_find::size_type unsigned_union_find::get_other(size_type a)
{
  check_index(a);
  a=find(a);

  // Cannot find another node in a singleton set
  PRECONDITION(nodes[a].count >= 2);

  // find a different member of the same set
  for(size_type i=0; i<size(); i++)
    if(find(i)==a && i!=a)
      return i;

//  UNREACHABLE;
  return 0;
}

void unsigned_union_find::intersection(
  const unsigned_union_find &other)
{
  unsigned_union_find new_sets;

  new_sets.resize(std::max(size(), other.size()));

  // should be n log n

  for(size_type i=0; i<size(); i++)
    if(!is_root(i))
    {
      size_type j=find(i);

      if(other.same_set(i, j))
        new_sets.make_union(i, j);
    }

  swap(new_sets);
}

unsigned_union_find::size_type unsigned_union_find::find(size_type a) const
{
  if(a>=size())
    return a;

  while(!is_root(a))
  {
    // one-pass variant of path-compression:
    // make every other node in path
    // point to its grandparent.
    nodes[a].parent=nodes[nodes[a].parent].parent;

    a=nodes[a].parent;
  }

  return a;
}
