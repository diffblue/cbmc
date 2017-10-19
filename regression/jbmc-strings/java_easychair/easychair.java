public class easychair
{
   public static void main(String[] argv)
   {
      if(argv.length > 1)
      {
         String str = new String(argv[1]);
         if(str.length() < 40)
         {
            // containing "/" and containing "EasyChair"
            int lastSlash = str.lastIndexOf('/');
            if(lastSlash < 0) return ;

            String rest = str.substring(lastSlash + 1);
            // warning: removed this because contains is not efficient at the moment
            if(! rest.contains("EasyChair")) return ;
            // (2) Check that str starts with "http://"
            if(! str.startsWith("http://")) return ;
            // (3) Take the string between "http://" and the last "/".
            // if it starts with "www." strip the "www." off
            String t = str.substring("http://".length(),lastSlash - "http://".length());
            if(t.startsWith("www."))
            t = t.substring("www.".length());

            //(4) Check that after stripping we have either "live.com"
            // or "google.com"
            if(!t.equals("live.com") && !t.equals("google.com"))
               return ;
            // s survived all checks
            assert(false); //return true;
         }
      }
   }
}
