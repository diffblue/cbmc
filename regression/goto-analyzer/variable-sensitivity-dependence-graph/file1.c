struct structt
{
  int a;
  int b;
};

extern struct structt st;
extern int in;
int out1, out2, out3;

void struct_task(void)
{
  int i;
  if(in == 1)
    st.a++;

  if(in == 2)
    st.b++;

  out1 = st.a;
  out2 = st.b;
  out3 = st.a + st.b;
}
