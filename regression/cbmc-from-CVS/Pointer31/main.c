int nondet_int();

int *p;
int global;

int main()
{
  p=&global;
  
  for(int i=0; i<10; i++)
  {
    *p=1;

    // this is not allowed!    
    int local;
    p=&local;
  }
}
