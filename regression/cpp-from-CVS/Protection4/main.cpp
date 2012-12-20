struct A
{
	private:
	int i;
};

class B: public A
{
	public:
	void set(int i){this->i = i;}
	int get() const {return i;}
};

