package distancebetweenmins;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

public class Distance {
    public static void main(String[] args) throws Exception {

        List<Integer> list = readUserInput();
        for (Integer i : list) {
            System.out.print(i + " ");
        }
        List<Integer> minsPositions = findMins(list);        

        List<Integer> result = getDistance(minsPositions);
        System.out.println();
        System.out.println("Distance between minimums: ");
        
        for (Integer element : result)
            System.out.print(element + " ");

    }

    private static List<Integer> readUserInput() throws Exception {

        List<Integer> list = new ArrayList<Integer>();
        BufferedReader reader = new BufferedReader(new InputStreamReader(
                System.in));

        String string = reader.readLine();
        String[] strings = string.split(" ");
        try {
            for (int i = 0; i < strings.length; i++) {
                list.add(Integer.parseInt(strings[i]));
            }
        } catch (Exception e) {
            System.out.println(e);
        }
        return list;
    }

    private static List<Integer> findMins(List<Integer> list) {
        int min = list.get(0);
        List<Integer> minimums = new ArrayList<Integer>();
        for (int i = 0; i < list.size(); i++) {
            if (min > list.get(i)) {
                min = list.get(i);
            }
        }
        for (int i = 0; i < list.size(); i++) {
            if (list.get(i) == min)
                minimums.add(i);
        }

        if (minimums.size() < 2) {
            int min2 = list.get(0);
            for (int i = 0; i < list.size(); i++) {
                if (minimums.contains(i)) {
                    break;
                } else {
                    if (min2 < list.get(i)) {
                        min2 = list.get(i);
                    }
                }
            }

            for (int i = 0; i < list.size(); i++) {
                if (list.get(i) == min2)
                    minimums.add(i);
            }
        }
        return minimums;
    }

    private static List<Integer> getDistance(List<Integer> list) {
        List<Integer> dist = new ArrayList<Integer>();
        int difference = 0;
        for (int i = 0; i < list.size() - 1; i++) {
            for (int j = 1; j < list.size(); j++) {
                difference = Math.abs(list.get(i) - list.get(i + 1));
                dist.add(difference);
            }
        }
        return dist;
    }
}
