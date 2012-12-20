class I
{
	int i;
	public:
	int get(){return i;}
	void set(int i){this->i=i;}
	I& operator<<=(const I& ref){i <<= ref.i; return *this;}
	I& operator>>=(const I& ref){i >>= ref.i; return *this;}
	I& operator+=(const I& ref){i += ref.i; return *this;}
	I& operator-=(const I& ref){i -= ref.i; return *this;}
};

int main()
{
	I i1, i2;
	i1.set(1);
	i2.set(2);
	i2+=i1;
	assert(i2.get()==3);
	i2-=i1;
	assert(i2.get()==2);
	i2 <<= i1;
	assert(i2.get()==4);
	i2 >>= i1;
	assert(i2.get()==2);
	i2 = i1;
	assert(i2.get()== 1);
}
