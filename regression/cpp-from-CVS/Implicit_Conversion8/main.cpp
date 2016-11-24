struct Bit {
	bool b;
	Bit(bool b=false):b(b){}
	Bit(const Bit& bit):b(bit.b){}

//	operator bool() const {return b;}

	Bit& operator=(bool b)
	{
	   this->b = b;
	   return *this;
        }


        Bit& operator =(const Bit& bit)
        {
	   this->b = bit.b;
	   return *this;
        }


	friend const Bit operator ~(const Bit& bit)
	{
		Bit r;
		r.b = ~bit.b;
		return r;
	}

	friend void b_not( Bit& r, const Bit& a )
	{ r = (~a); }
};


int main()
{
	Bit b1, b2;
	b_not(b1,b2);
	assert(b1.b != b2.b);
}

