 struct ostream
  {
    ostream(int id): id(id){}
    ostream(const ostream&); // disabled
    ostream& operator=(const ostream&); // disabled
    int id;
  };

  struct istream
  {
    istream(int id): id(id){}
    istream(const istream&); // disabled
    istream& operator=(const istream&); // disabled
    int id;
  };

  struct iostream: ostream, istream
  {
    iostream(int id): ostream(id), istream(id) {}
    iostream(const iostream&); // disabled
    iostream& operator=(const iostream&); // disabled
  };


int main()
{
  iostream io(1);
  assert(io.ostream::id == 1);
  assert(io.istream::id == 1);
}
