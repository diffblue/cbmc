class A
{
	int a;
};

int f(A* pa, char i){return i+1;}

int main()
{
	int (A::* paf)(char) = &f; // ill-formed
}
