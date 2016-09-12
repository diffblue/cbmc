public class test_index_of {

    public static void main(String[] argv) {
	String s = "Hello World!"; 
	char c = 'o';
	int i = s.indexOf(c);
	int j = s.lastIndexOf('o');
	assert(i == 4);
	assert(j == 7);	

	if(argv.length > 1)
	    assert(i != 4);
	else
	    assert(j != 7);
    }
}
