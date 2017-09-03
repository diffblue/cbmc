// from
// http://www.thegeekstuff.com/2010/02/java-hello-world-example-how-to-write-and-execute-java-program-on-unix-os/

/* Hello World Java Program */
class helloworld  {
    public static void main(String[] args) {
        assert(System.out != null);
        System.out.println("Hello World!");
        assert(System.err != null);
        System.err.println("Hello World!");
        assert(System.in != null);
        try {
          int avail = System.in.available();
        }
        catch(java.io.IOException e) {}
    }
}
