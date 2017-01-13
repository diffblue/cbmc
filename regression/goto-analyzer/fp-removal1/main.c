void f1 (void) { int tk = 1; }
void f2 (void) { int tk = 2; }
void f3 (void) { int tk = 3; }
void f4 (void) { int tk = 4; }
void f5 (void) { int tk = 5; }
void f6 (void) { int tk = 6; }
void f7 (void) { int tk = 7; }
void f8 (void) { int tk = 8; }
void f9 (void) { int tk = 9; }

typedef void(*void_fp)(void);

// There is a basic check that excludes all functions that aren't used anywhere
// This ensures that check can't work in this example
void_fp fp_tbl[] = {f1, f2 ,f3, f4, f5 ,f6, f7, f8, f9};

void func1()
{
  void_fp fp = f2;
  fp();
}

void main(){
   for(int i=0;i<3;i++){
     func1(i,0);
   }
}
