class A
{
	public:
	void f(int i){}
	void f(){A::f(0);}
};

int main(){}
