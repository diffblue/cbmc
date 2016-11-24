struct Char {
	char c;
	Char(char c):c(c){}
};

struct Int {
	int i;
	operator int& ();
	Int(int i):i(i){}
};

Int::operator int&(){return i;}

int  main()
{
   Int I1(1);
   int i1 = int(I1);
   assert(i1==1);

   
   Int I2(2);
   int i2 = (int&)I2;
   assert(i2==2);


   Int I3(3);
   int i3 =0;
   i3  = I3;
   assert(i3==3);

   Char C3(I3);
   assert(C3.c==3);
}
