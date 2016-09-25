#include <cassert>
#include <vector>
#include <string>

#include <util/string_utils.h>

int main()
{
  assert(strip_string("   x y ")=="x y");

  const std::string test=" a,, x , ,";

  std::vector<std::string> result;
  split_string(test, ',', result, false, false);
  assert(result.size()==5);
  assert(result[0]==" a");
  assert(result[1]=="");
  assert(result[2]==" x ");
  assert(result[3]==" ");
  assert(result[4]=="");

  result.clear();
  split_string(test, ',', result, true, false);
  assert(result.size()==5);
  assert(result[0]=="a");
  assert(result[1]=="");
  assert(result[2]=="x");
  assert(result[3]=="");
  assert(result[4]=="");

  result.clear();
  split_string(test, ',', result, false, true);
  assert(result.size()==3);
  assert(result[0]==" a");
  assert(result[1]==" x ");
  assert(result[2]==" ");

  result.clear();
  split_string(test, ',', result, true, true);
  assert(result.size()==2);
  assert(result[0]=="a");
  assert(result[1]=="x");

  std::string s1;
  std::string s2;
  split_string("a:b", ':', s1, s2, false);
  assert(s1=="a");
  assert(s2=="b");
}

