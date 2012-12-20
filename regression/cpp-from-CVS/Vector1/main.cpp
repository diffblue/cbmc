#include <vector>
using namespace std;

/*
void sort(vector<int>& c)
{
	if (c.begin() == c.end()) return;
	
	for(int i=0; i < c.size(); i++)
	{
		for(vector<int>::iterator it = c.begin();
				it < c.end() ;
				it++)
		{
			vector<int>::iterator it_inc = it;
			it_inc++;

			if(it_inc == c.end())
				break;
		
			if(it_inc < it)
			{
				vector<int>::value_type tmp = * it;
				*it = *it_inc;
				*it_inc = tmp;
			}
		}
	}
}
*/
int main()
{
	vector<int> vec;
	vec.resize(0);
	__CPROVER_assert(vec.size()==0, "vec size == 0");
/*	vec.push_back(2);
	vec.push_back(1);
	vec.push_back(4);

	sort(vec);

	for(vector<int>::iterator it = vec.begin(); it < vec.end(); it++)
	{
		vector<int>::iterator it_inc = it;
		it_inc++;
		
		if(it_inc == vec.end()) break;
		__CPROVER_assert(*it <= *it_inc, "sorting error");
	}
*/
}
