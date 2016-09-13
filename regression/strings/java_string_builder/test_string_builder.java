public class test_string_builder {
    public static void main(String[] argv) {
	if(argv.length > 2) {
	    StringBuilder tmp = new StringBuilder(); 
	    tmp.append("prefix ");
	    tmp.append(argv[1]);
	    tmp.append(" middle ");
	    tmp.append(argv[2]);
	    tmp.append(" end");
	    String r = tmp.toString();
	    assert(r.startsWith("pref"));	    
	    assert(r.endsWith("end"));
	    assert(r.startsWith("pr3f"));
	}
    }
}
