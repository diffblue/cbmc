struct structt
{
  int a;
  int b;
};

struct structt st;
int ar[2];
int arr[3];

extern int in;
int out1, out2, out3;

void struct_task(void);
void array_task(void);

void main(void)
{
  if(in == 1)
    st.a++;

  if(in == 2)
    st.b++;

  out1 = st.a;
  out2 = st.b;
  out3 = st.a + st.b;

  if(in == 1)
    ar[0]++;

  if(out1 == 2)
    ar[1]++;

  out1 = ar[0];
  out2 = ar[1];
  out3 = ar[0] + ar[1];

  arr[0] = 1;
  arr[1] = 2;
  arr[2] = 3;

  if(in > 0)
  {
    arr[2] = arr[1];
  }

  out1 = arr[0];
  out2 = arr[1];
  out3 = arr[2];

  struct_task();
  out1 = st.a;
  out2 = st.b;
  out3 = st.a + st.b;

  array_task();
  out1 = ar[0];
  out2 = ar[1];
  out3 = ar[0] + ar[1];
}
