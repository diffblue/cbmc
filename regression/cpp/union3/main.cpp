struct A {
	static union    // static is not allowed here
	{
		int a;
		char b;
	};

};
