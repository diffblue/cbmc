//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//Listing 2. A nonblocking counter using CAS

#define __VERIFIER_atomic_CAS(v, e, u, r, flag) \
{ \
  __CPROVER_atomic_begin(); \
	if(*v == e) \
	{ \
		*flag = 1, *v = u, *r = 1; \
	} \
	else \
	{ \
		*r = 0; \
	} \
  __CPROVER_atomic_end() ; \
}

volatile unsigned value = 0;

/*helpers for the property*/
volatile unsigned inc_flag = 0;
volatile unsigned dec_flag = 0;

void X__VERIFIER_atomic_assert1(unsigned inc__v)
{
  __CPROVER_atomic_begin();
  unsigned inc__v_l=inc__v;
  unsigned dec_flag_l=dec_flag;
  unsigned value_l=value;
  __CPROVER_atomic_end();
	__CPROVER_assert(dec_flag_l || value_l > inc__v_l, "");
}

unsigned inc() {
	unsigned inc__v, inc__vn, inc__casret;

	{
		inc__v = value;

		if(inc__v == 0u-1) {
			return 0; /*increment failed, return min*/
		}

		inc__vn = inc__v + 1;

		__VERIFIER_atomic_CAS(&value,inc__v,inc__vn,&inc__casret,&inc_flag);
	}
	__CPROVER_assume(! (inc__casret==0));

  X__VERIFIER_atomic_assert1(inc__v);

	return inc__vn;
}

void X__VERIFIER_atomic_assert2(unsigned dec__v)
{
  __CPROVER_atomic_begin();
  unsigned dec__v_l=dec__v;
  unsigned inc_flag_l=inc_flag;
  unsigned value_l=value;
  __CPROVER_atomic_end();
  __CPROVER_assert(inc_flag_l || value_l < dec__v_l, "");
}

unsigned dec() {
	unsigned dec__v, dec__vn, dec__casret;

	{
		dec__v = value;

		if(dec__v == 0) {
			return 0u-1; /*decrement failed, return max*/
		}

		dec__vn = dec__v - 1;

		__VERIFIER_atomic_CAS(&value,dec__v,dec__vn,&dec__casret,&dec_flag);

	}
	__CPROVER_assume(! (dec__casret==0));

  X__VERIFIER_atomic_assert2(dec__v);
	return dec__vn;
}

int main(){
__CPROVER_ASYNC_1: inc();
__CPROVER_ASYNC_2: dec();
__CPROVER_ASYNC_3: dec();

  return 0;
}
