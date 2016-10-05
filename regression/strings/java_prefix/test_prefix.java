public class test_prefix {

    public static void main(String[] argv) {
	String s = new String("Hello World!");
	//String t = new String("Hello");
	//String u = new String("Wello");
	String u = "Wello";
	boolean b = s.startsWith("Hello");
	//boolean c = s.startsWith("Wello");
	//boolean b = s.startsWith(t);
	boolean c = s.startsWith(u);
	boolean d = s.startsWith("lo",3);
	if(argv.length == 1){
	    assert(b);	
	} else if(argv.length == 2){
	    assert(c);
	} else if(argv.length == 3){
	    assert(d);
	} else if(argv.length == 4){	
	    assert(!d);
	}
    }
}
