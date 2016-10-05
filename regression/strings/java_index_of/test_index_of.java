public class test_index_of {

    public static void main(String[] argv) {
	String s = "Hello World!"; 
	char c = 'o';
	int i = s.indexOf(c);
	int j = s.lastIndexOf('o');
	int k = s.indexOf(c,5);
	if(argv.length == 1){
	    assert(i == 4);
	    assert(i != 4);
	}
	else if(argv.length == 2){
	    assert(j == 7);	
	    assert(j != 7);
	}
	else {
	    assert(k == 7);
	    assert(k != 7);
	}
    }
}
