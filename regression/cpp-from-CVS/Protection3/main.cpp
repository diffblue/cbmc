class A
{
	int i;
	
	public:
	class B
	{
		int get(const A& a){return a.i;}
	};
};
