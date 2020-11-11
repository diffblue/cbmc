struct Ages
{
  int x;
  int y;
};

void do_structs()
{
  int bool_;
  int bool_1;
  int bool_2;

  struct Ages st;

  // Simple variables.
  st.x = 10;
  st.y = 20;
  st.x = 30;
  st.y = 40;
  st.y = st.x;
  st.x = st.y;
  st.x = 5;
  st.x = st.x + 10;
  st.y = 10;

  if(bool_)
  {
    st.x = 20;
  }
  else
  {
    st.x = 20;
  }

  st.x = 0;

  if(bool_1)
  {
    st.x = 3;
    if(bool_2)
    {
      st.x = 5;
    }
  }
  else
  {
    st.x = 7;
  }
  st.y = 10;
  st.x = 20;

  struct Ages new_age;

  new_age = st;
}

int main()
{
  do_structs();
}
