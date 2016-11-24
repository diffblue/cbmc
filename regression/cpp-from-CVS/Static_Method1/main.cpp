struct A
{
	static int Value(int v){return v;}
	static int Value(int v1, int v2){return 1;}
};

int main()
{
	A a;
	assert(a.Value(0) == 0);
}
