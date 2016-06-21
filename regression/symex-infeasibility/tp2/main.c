struct state_element_f{
	unsigned int x;
	unsigned int diff;
	unsigned int add;
};

unsigned int f(unsigned int t, struct state_element_f stf)
{
	unsigned int m1;
	if(t>1) {
                stf.x=1;
		stf.diff=1;
		m1=1;
	}
	else {
		stf.add=1;
	  m1=0;
	}
  return t;
}

struct state_element_g{
	unsigned int y;
	unsigned int avg;
	unsigned int sum;
};

void g(unsigned int k, struct state_element_g stg)
{
	unsigned int m2;
	if(k>1) {
		stg.y=1;
		stg.avg=1;
		m2++;
	}
	else {
		stg.sum=1;
		m2--;
	}
}

void main()
{
	//*****************************************************
	// Total Paths = 2, Feasible Path=2, Infeasible Path=0
	// ****************************************************
	unsigned int m, n;
  // Structures are passed as function arguments to build the harness
  struct state_element_f stf;
  struct state_element_g stg;
	// Identify and bind equivalent signals in both design to allow partitioning
	m=nondet_unsigned();
	n=f(m,stf);
	g(n,stg);
	assert(1);
  //****************************************************
}
