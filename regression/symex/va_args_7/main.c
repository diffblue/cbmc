#include <stdio.h> 
#include <stdarg.h> 
#include <assert.h> 

int main ()
{
    
  int eva_arguments;
  int n;

  int init_eva = eva_arguments;

  for (unsigned int i = 0; i < n; i++){
  
    eva_arguments++;  
  }

  if (init_eva == 0){
    assert(eva_arguments == n);  
  }

  return 0;
}
