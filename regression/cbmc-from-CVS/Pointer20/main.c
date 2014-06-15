int nondet_int();

int *p;
int global;

void f() {
  int local;
  int input;
  
  input=nondet_int();

  p=input?&local:&global;
}

int main() {
  int z;

  f();

  z=*p;
}
