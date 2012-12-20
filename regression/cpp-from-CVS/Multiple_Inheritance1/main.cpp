struct A
{
	int i;
};

struct B {
	int j;
	void setJ(int j){this->j = j;}
};


struct C: A, B {
	int k;
};

int main()
{
	C c;
	c.setJ(10);
	assert(c.j==10);
}
