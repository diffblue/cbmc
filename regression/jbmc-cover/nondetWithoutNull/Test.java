// This file needs to be compiled with
// src/java_bytecode/library/src/org/cprover/CProver.java
import org.cprover.CProver;

public class Test {
    public final static Object stat = CProver.nondetWithoutNull();
    
    public static int check() {
	Object o = CProver.nondetWithoutNull();

	if(stat == null)
	    return -1;

	if(o == null)
	    return 0;

	return 1;
    }

    public static int check2() {
	Integer i = CProver.nondetWithNull();

	if(i == null)
	    return -1;
	
	if(i instanceof Integer)
	    return 0;

	return 1;
    }

}
