public class test_init {

  public static void main(/*String[] argv*/)
  {
     char [] str = new char[10];
     str[0] = 'H';
     str[1] = 'e';
     str[2] = 'l';
     str[3] = 'l';
     str[4] = 'o';
     String s = new String(str);
     String t = new String(str,1,2);

     System.out.println(s.length());
     assert(s.length() == 10);
     System.out.println(s);
     System.out.println(t);
     assert(t.equals("el"));
     assert(s.startsWith("Hello"));
   }
}
