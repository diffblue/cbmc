public class ArrayIndexOutOfBoundsExceptionTest {
    public static void main(String args[]) {
	try {
	    int[] a=new int[4];
	    a[6]=0;
	    // TODO: fix the bytecode convertion such that there is no need for
	    // an explicit throw in order to convert the handler
	    throw new RuntimeException();
	}
	catch(ArrayIndexOutOfBoundsException exc) {
	    assert false;
	}
    }
}
