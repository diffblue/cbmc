package euler;
import java.util.ArrayList;

public class Problem3 {

	public static ArrayList<Integer> primesUpToN(int n) {
		ArrayList<Integer> list = new ArrayList<Integer>();
		if (n < 2) {
			return list;
		}
		list.add(2);
		boolean foundmatch;
		for (int i = 3; i < n; i += 2) {
			if ((i-1)%100000==0){
				//System.out.println(i);
				//System.out.println(list.size());
			}
			foundmatch = false;
			for (Integer j : list) {
				if (j *j > i){
					break;
				}
				if ((i-1)%100000==0){
					//System.out.println(j);
				}
				if (i % j == 0) {
					foundmatch = true;
					break;
				}
			}
			if (!foundmatch) {
				list.add(i);
			}
		}
		return list;
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		ArrayList<Integer> list = new ArrayList<Integer>();
		list.add(2);
		boolean foundmatch;
		long mynum = 600851475143L;
		long orignum = mynum;
		for (int i = 3; i < Math.sqrt(orignum); i += 2) {
			foundmatch = false;
			for (Integer j : list) {
				if (i % j == 0) {
					foundmatch = true;
					break;
				}
			}
			if (!foundmatch) {
				System.out.println("Found:"+i);
				list.add(i);
				while (mynum % i == 0) {
					if (i == mynum){
						System.out.println(i);
						return;
					}
					mynum/=i;
				}
			}
		}

	}
}
