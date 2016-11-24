int x,y;

void function1(){
  x=1;
}

void function2(){
  y=1;
}

void function3(){
  __CPROVER_assert(x!=0 || y!=0, "SC");
}

void main(){
  x=0;
  y=0;

  __CPROVER_ASYNC_1: function1();
  __CPROVER_ASYNC_2: function2();
  __CPROVER_ASYNC_3: function3();
}
