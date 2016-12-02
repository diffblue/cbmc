public class test_sb_length {
    public static void main(String[] argv) {
	StringBuilder tmp = new StringBuilder("prefix"); 
	//tmp.append("prefix");
	tmp.append("end");
	assert(tmp.length() == 9);	    
	if(argv.length > 1) {
	    assert(tmp.length() == 12);	    
	}
    }
}
