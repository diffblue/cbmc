public class Solution {
    
    int k;
    int N;
    boolean FIND;
    
    HashSet<Integer> set = new HashSet<Integer>();
    ArrayList<Integer> list = new ArrayList<Integer>();
    ArrayList<Integer> bits = new ArrayList<Integer>();

    public ArrayList<Integer> grayCode(int n) {
        k = n;
        N = 1 << (k + 1) - 1;
        list = new ArrayList<Integer>();
        bits = new ArrayList<Integer>();
        
        for (int i = 0; i < N; i++)
            list.add(0);
        for (int i = 0; i < k; i++)
            bits.add(1 << i);

        FIND = false;
        set.clear();
        set.add(0);
        list.set(0, 0);
        findNext(0);
        return list;
    }

    public void findNext(int num){
        if (FIND)
            return;
        if (set.size() == N){
            FIND = true;
            return;
        }
        for (int i = 0; i < k; i++) {
            int temp = num ^ bits.get(i);
            if (set.contains(temp))
                continue;
            set.add(temp);
            list.set(set.size() - 1, temp);
            findNext(temp);
            set.remove(temp);
            if (FIND)
                break;
        }
    }
}