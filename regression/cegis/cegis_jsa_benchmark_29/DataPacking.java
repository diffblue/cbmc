import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Scanner;

/**
 * FileName: DataPacking.java
 * @Description:
 *
 * @author Xunhu(Tiger) Sun
 *         email: sunx2013@my.fit.edu
 * @date Jan 31, 2015 4:35:26 PM
 */
public class DataPacking {
    final Scanner sc = new Scanner(System.in);

    void read () {
        n = sc.nextInt();
        c = sc.nextInt();
        sc.nextLine();
        list = new LinkedList<Integer>();
        for(int i =0; i < n; i++){
            list.add(sc.nextInt());
        }
        Collections.sort(list,Collections.reverseOrder());
    }

    int n;
    int c;
    LinkedList<Integer> list;

    void solve () {
        int count = 0;
        while(!list.isEmpty()){
            int cur = list.removeFirst();
            int dif = c - cur;
            Iterator<Integer> it = list.iterator();
            while(it.hasNext()){
                int next = it.next();
                if(next <=dif){
                    it.remove();
                    break;
                }
            }
            count++;
        }
        System.out.println(count);
    }

    void run () {
        final int cn = sc.nextInt();
        sc.nextLine();
        for (int ci = 1; ci <= cn; ci++) {
            read();
            System.out.printf("Case #%d: ", ci);
            solve();
        }
    }

    public static void main (String[] args) {
        new DataPacking().run();
    }
}
