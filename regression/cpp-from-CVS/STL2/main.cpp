#include <vector>

bool nondet_bool();
int nondet_int();

using namespace std;

int main()
{
  vector<int> v;

  while(nondet_bool())
    v.push_back(nondet_int());

  vector<int>::iterator it;
  
  for(it = v.begin(); it != v.end(); it++)
    if(*it == 10) v.erase(it);
}
