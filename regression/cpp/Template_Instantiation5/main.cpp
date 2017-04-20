// #include <stdio.h>

template <typename T>
class template_test
{
public:
   T elem;
   template_test(T in)
   {
      elem = in;
   }
   T get(void)
   {
        // printf ("elem is '%c' \n", elem);
        return elem;
   }

   void add(void)
   {
        int c = elem + elem;
        // printf ("c = %d \n", c);
        return;
   }

   ~template_test()
   {
     elem=-1;
   }
};

int main (void)
{
    template_test<char> a('a');
    a.get();
    a.add();
    return 0;
}
