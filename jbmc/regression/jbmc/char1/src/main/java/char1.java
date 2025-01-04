class char1 {

  static public void doit(char my_char)
  {
    int x=my_char;
    assert x>=0 && x<='\uffff';

    my_char='\uffff';
    my_char++;
    assert my_char==0;
  }

};
