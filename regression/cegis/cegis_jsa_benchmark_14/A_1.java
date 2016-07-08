package by.it.veselov.JD01_12;
import java.util.ArrayList;
import java.util.Iterator;
/**
 * Created by yegorveselov on 10.03.16.
 */
public class A_1 {


        public static void main(String[] args)
        {

                int element = 5;
                int negative = 3;
                ArrayList<Integer> mark = new ArrayList<Integer>();
                for (int i = 0; i < element; i++)
                {
                    int a = (int)(Math.random() * 10 + 1);
                    Integer b = new Integer(a);
                    mark.add(i, b);
                }
                System.out.println(mark);
                for(Iterator<Integer> it = mark.iterator(); it.hasNext();)
                    if(it.next()<= negative)
                        it.remove();
                System.out.println(mark);
            }
}

