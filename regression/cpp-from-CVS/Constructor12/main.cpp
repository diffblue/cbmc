struct A
{
	int i;
	A():i(10){}
	private:
	A(const A& a); // disabled
};


class B:  A {
	public:
		B(){};
		int get_i(){return i;}
	private:
		B(B& b); // disabled
};

int main()
{
	B b;
	assert(b.get_i() == 10);
}
