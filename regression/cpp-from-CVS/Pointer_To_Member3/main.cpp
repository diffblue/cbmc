class A
{
	public:
	int a;
	int f(char i){return i+1;}
};


int main()
{
	int (* pf)(A*, char) = &A::f; // ill-formed
}
