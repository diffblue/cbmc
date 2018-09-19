#include <cassert>

template <class T>
class sc_signal
{
public:
    T data;
    sc_signal(){}
    sc_signal(const char *p) {}
    T read() {return data;}
    void write(const T &d) {data = d;}
};


struct rbm
{

   sc_signal<unsigned int>  data_out;   //<L1>

   sc_signal<bool>   done;  // <L2>

   sc_signal<bool> conf_done;

   void config();

   rbm()
   {

   }

};


void rbm::config()
{
   do {
         conf_done.write(true);
         assert(conf_done.data==true);
    } while ( !conf_done.read() );
}

int main()
{
    rbm IMPL;
    IMPL.config();

    return 0;
}
