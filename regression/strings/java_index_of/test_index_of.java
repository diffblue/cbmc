public class test_index_of {

    public static void main(String[] argv) {
	String s = "Hello World!"; 
	char c = 'o';
	int i = s.indexOf(c);
	int j = s.lastIndexOf('o');
	int k = s.indexOf(c,5);
	int l = s.lastIndexOf(c,5);
	int m = s.indexOf("lo");
	int n = s.lastIndexOf("lo");
	if(argv.length == 1){
	    assert(i == 4);
	    assert(i != 4);
	}
	else if(argv.length == 2){
	    assert(j == 7);	
	    assert(j != 7);
	}
	else if(argv.length == 3){
	    assert(k == 7);
	    assert(k != 7);
	}
	else if(argv.length == 4){
	    assert(l == 4);
	    assert(l != 4);
	} else {
	    assert(m != 2);
	    assert(n != 2);
	}
    }
}
