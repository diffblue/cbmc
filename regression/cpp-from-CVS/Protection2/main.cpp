struct A
{
	protected:
	int i;
};

class B: A
{
	public:
	void set(int i){this->i = i;}
	int get() const {return i;}
};

int main()
{
	B b;
	b.set(0);
	assert(b.get()== 0);
}
