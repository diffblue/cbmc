/**
 * 
 */
package up.teach.dm.mapreduce.examples;

import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

import up.teach.dm.mapreduce.IMapFunction;
import up.teach.dm.mapreduce.IReduceFunction;
import up.teach.dm.mapreduce.KeyValuePair;
import up.teach.dm.mapreduce.MapReduceJob;
import up.teach.dm.mapreduce.Master;
import up.teach.dm.utils.FileUtils;

/**
 * @author Robin Senge [robin.senge@uni-paderborn.de]
 */
public class DistributedNumberOfInboundEdges {

	public static void main(String[] args) throws Exception {

		final IMapFunction<Integer, Integer, Integer, Integer> map = new IMapFunction<Integer, Integer, Integer, Integer>() {

			@Override
			public List<KeyValuePair<Integer, Integer>> map(Integer source, Integer target) {

				List<KeyValuePair<Integer, Integer>> intermediateKeyValuePairs = new LinkedList<>();

				intermediateKeyValuePairs.add(new KeyValuePair<Integer, Integer>(target, 1));

				return intermediateKeyValuePairs;


			}
		};

		IReduceFunction<Integer,Integer,Integer,Integer> reduce = new IReduceFunction<Integer,Integer,Integer,Integer>() {

			@Override
			public List<KeyValuePair<Integer,Integer>> reduce(Integer key, List<Integer> values) {

				List<KeyValuePair<Integer, Integer>> finalKeyValuePairs = new LinkedList<KeyValuePair<Integer, Integer>>();
				int count = 0;
				for (Integer value : values) {
					count += value;
				}
				finalKeyValuePairs.add(new KeyValuePair<Integer, Integer>(key, count));

				return finalKeyValuePairs;

			}
		};

		// get data
		List<KeyValuePair<Integer, Integer>> edges = FileUtils.loadIntegerPairs("data/p2p-Gnutella04.txt");
		
		// run
		MapReduceJob<Integer, Integer, Integer, Integer, Integer, Integer> job = new MapReduceJob<>(map, reduce, edges);

		new Master(20, 20, 5).run(job);
		
		// sort
		Collections.sort(job.getResult(), new Comparator<KeyValuePair<Integer, Integer>>() {

			@Override
			public int compare(KeyValuePair<Integer, Integer> o1,
					KeyValuePair<Integer, Integer> o2) {
				return -Integer.compare(o1.getValue(), o2.getValue());
			}
			
		});
		
		// print output
		int i = 1;
		for (KeyValuePair<Integer, Integer> keyValuePair : job.getResult()) {
			System.out.println(keyValuePair);
			if(i++ >= 5) break;
		}




	}

}
