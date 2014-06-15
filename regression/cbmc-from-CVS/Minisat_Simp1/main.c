double fabs(double);
int isnan(double);

int main()
{
  double my_d, dabs;
  
  __CPROVER_assume(!isnan(my_d));
 
  dabs=(my_d<0)?-my_d:my_d;
  assert(fabs(my_d)==dabs);
}

