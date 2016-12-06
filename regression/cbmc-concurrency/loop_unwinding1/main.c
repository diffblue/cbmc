void* thr1 (void* arg)
{
  __CPROVER_assert(0, "");

  return 0;
}

int main(){
  __CPROVER_ASYNC_1: thr1(0);
	for(int i=0; i<5; ++i) ;
}
