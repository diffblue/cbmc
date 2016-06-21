struct state_element_f{
	unsigned int x; // Mode Variable
	unsigned int diff;
	unsigned int add;
};

unsigned int f(unsigned int t, struct state_element_f stf)
{
	unsigned int m1;
	if(t==1) {
		//t=1; //extra logic
		stf.diff=1;
		m1=1;
	}
	else if(t==2){
		//t=2; //extra logic
		stf.add=1;
	  m1=0;
	}
	else if(t==3){
		//t=3; //extra logic
		stf.add=0;
	  m1=1;
	}
  else { }; //t= 4; }
  return t;
}

struct state_element_g{
	unsigned int y; // Mode Variable
	unsigned int avg;
	unsigned int sum;
};

void g(unsigned int z, struct state_element_g stg)
{
	unsigned int m2;
	if(z==1) {
		z=1; //extra logic
		stg.avg=1;
		m2++;
	}
	else if(z==2){
		z=2; //extra logic
		stg.sum=1;
		m2--;

		// redundant logic
		if(m2==1)
			m2*=2;
		else
			m2/=2;
	}
	else if(z==3) {
		z=3; //extra logic
	  stg.sum=0;
	}
	//**********
	else {
          z = 4;
        }
	//**********
}

void main()
{
	//*******************************************************
	// Total Paths = 19, Feasible Path=3, Infeasible Path=16
	// ******************************************************

	unsigned int m,n;
  // Structures are passed as function arguments to build the harness
  struct state_element_f stf;
  struct state_element_g stg;
	//__CPROVER_assume(0);
	// Identify and bind equivalent signals in both design to allow partitioning
	/*if(nondet_bool())
	{
	  m=1;
	  n=1;
	}
	else if(nondet_bool())
	{
		m=2;
		n=2;
	}
	else if(nondet_bool())
	{
	  m=3;
		n=3;
	}
	else {
	  __CPROVER_assume(m==n);
	}*/
//	__CPROVER_assume(m==n);
        m=nondet_unsigned();
	n=f(m,stf);
	//n=m;
	g(n,stg);
	assert(1);
  //****************************************************

 	//*****************************************************
	// Total Paths = 16, Feasible Path=16, Infeasible Path=0
	// ****************************************************
	/*unsigned int m;
  // Structures are passed as function arguments to build the harness
  struct state_element_f stf;
  struct state_element_g stg;
	f(m,stf);
	g(m,stg);
	assert(1);*/
  //****************************************************

  //*****************************************************************************
	// When the last else of g() contains the extra code of if-else statement, then
	// Total Paths = 44, Feasible Path=1, Infeasible Path=43
	// ****************************************************************************
	/*unsigned int m;
  // Structures are passed as function arguments to build the harness
  struct state_element_f stf;
  struct state_element_g stg;
	// Identify and bind equivalent signals in both design to allow partitioning
	__CPROVER_assume(stf.x == 1 && stg.y == 1);
	f(m,stf);
	g(m,stg);
	assert(1);*/
  //****************************************************
}
