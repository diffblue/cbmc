class A
{
	public:
	int i;
};

class B: A
{
	
};

void set_one(A& a)
{
	a.i = 1;
}

int main()
{
	B b;
	set_one(b);
}
