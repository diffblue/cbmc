#include <vector>
#include <list>
#include <set>

struct X
{
  int i;
};

void test_vector()
{
  std::vector<int> int_vector;
  std::vector<int>::const_iterator it;

  int_vector.push_back(1);
  int_vector.push_back(2);
  assert(int_vector.front()==1);
  assert(int_vector.back()==2);
  assert(*int_vector.begin()==1);
  it=int_vector.begin();
  assert(*it==1);
  
  int_vector.pop_back();  
  int_vector.pop_back();  
  assert(int_vector.empty());
}

void test_list()
{
  std::list<int> int_list;
  
  int_list.push_back(1);
  int_list.push_back(2);
  assert(int_list.front()==1);
  assert(int_list.back()==2);
  assert(*int_list.begin()==1);
  
  int_list.pop_back();  
  int_list.pop_back();  
  assert(int_list.empty());
}

void test_set()
{
}

int nondet_int();

int main()
{
  switch(nondet_int())
  {
  case 0: test_vector(); break;
  case 1: test_list(); break;
  case 2: test_set(); break;
  
  default:;
  }
}
