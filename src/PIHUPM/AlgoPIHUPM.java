package PIHUPM;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

/**
 * This is an implementation of the
 * "EIHI" algorithm by Fournier-Viger et al. (2015).
 * 
 * @see UtilityList
 * @see Element
 * @author Philippe Fournier-Viger
 */
public class AlgoPIHUPM {

	/** the maximum memory usage */
	public double maxMemory = 0;    
	/** the time the algorithm started */
	public long startTimestamp = 0; 
	/** the time the algorithm terminated */
	public long endTimestamp = 0;   
	/**  the number of HUI generated */
	public int huiCount =0;  
	
	/** Store the total times for all runs of this algorithm */
	public long totalTimeForAllRuns = 0;
	/** The number of candidates processed by the algorithm  for all updates (runs)*/
	public int totalCandidateCountForAllRuns = 0;
	
	/** The number of transactions processed until now by the algorithm */
	public int transactionCount;
	
	public int candidateCount =0;
	
	/** Map to remember the TWU of each item */
	Map<Integer, Integer> mapItemToTWU;
	
	/** During first database, the item are sorted by TWU.... Then we keep this ordering
	* in the following map because if the ordering change in an updated database,
	*  then the result may be incorrect. */
	Map<Integer, Integer> mapItemToRank;

	/** This is a map to store the utility-list of each item from the database*/
	private Map<Integer, UtilityList> mapItemToUtilityList;

	/** This is a list of all utility-lists of single items */
	List<UtilityList> listOfUtilityLists;

	/** The first line to be read from the input file*/
	int firstLine;
	
	/** A buffer for storing the current itemset that is mined when performing mining
	*  the idea is to always reuse the same buffer to reduce memory usage.
	**/
	private int[] itemsetBuffer = null;
	/** The initial buffer size */
	final int BUFFERS_SIZE = 400;
	
	/** this class represent an item and its utility in a transaction */
	class Pair{
		Pair(int item, int utility){
			this.item = item;
			this.utility = utility;
		}
		/** An item */
		int item = 0;
		/** The utility of the item in a given transaction*/
		int utility = 0;
		
		/** 
		 * Return a String representation of this "pair" object. This is useful for debuging.
		 * @return the string representation
		 */
		public String toString() {
			return "[" + item + "," + utility + "]";
		}
	}
	class Infor{
		int Large;
		int Pre_lage;
	}
	
	//****************************** TRIE *******************************************//
	//    The following code is for implementing the HUI-TRIE structure used in that //
	//    algorithm.                                                                 //
	//*******************************************************************************//
	
	/** This is the list of child of the root node in the trie. Actually the root
	 * node is not represented.
	 */
	List<Node> singleItemsNodes;
	
	/**
	 * This class is a node of the HUI-Trie.
	 */
	public class Node{
		/** An item stored in this node*/
		int item;
		/** The list of child node */
		List<Node> childs = new ArrayList<Node>(3);
		/** A utility value stored in that node */
		int utility = -1;
		  
		/** The node constructor
		 * @param item an item
		 */
		public Node(int item) {
			this.item = item;
		}
		
		/**
		 * Alternative constructor
		 * @param item the item to store in that node
		 * @param utility the utility to store in that node
		 */
		public Node(int item, int utility) {
			this.item = item;
			this.utility = utility;
		}
	}

	/**
	 * Get the number of HUIs stored in the HUI-trie structure. This
	 * is performed by scanning the HUI-Trie and checking which itemsets
	 * are HUIs.
	 * @return the number of HUIs.
	 */
	public Infor getRealHUICount() {
		// call the recursive method for counting using all the childs of the root note
		return getRealHUICount(singleItemsNodes);
	}
	
	/**
	 * This is a helper method to count the number of HUIs stored in the HUI-trie structure.
	 * @param  list a list of nodes to explore in a depth-first search way to count the HUIs.
	 * @return the number of HUIs.
	 */
	public Infor getRealHUICount(List<Node> list) {
		Infor info = new Infor();
		// for each node
		for(Node node : list) {
			// if it represents a HUI
			if(node.utility >= minUtility_upper) {
				// increase the count
				info.Large++;
			}else{
				if(node.utility >= minUtility_lower) {
					info.Pre_lage++;
				}
			}
			// explore childs of that node
			info.Large += getRealHUICount(node.childs).Large;
			info.Pre_lage += getRealHUICount(node.childs).Pre_lage;
		}
		// return the total count
		return info;
	}
	

	/**
	 * Print all HUIs stored in the trie to the console.
	 */
	public void printHUIs() {
		// Make a recursive call to the helper method using childs of the root node.
		System.out.println("Large: ");
		print_Large_Itemset(singleItemsNodes, "");
		System.out.println("Pre_Large: ");
		print_Pre_Large_Itemset(singleItemsNodes, "");
	}
	
	/**
	 * Recursive method to print all HUIs stored in the trie to the console.
	 * @param list a list of nodes to explore in a depth-first search way
	 * @param prefix the current prefix, which is the concatenation of all items in the current
	 * branch of the tree.
	 */
	public void print_Pre_Large_Itemset(List<Node> list, String prefix) {
		for(Node node : list) {
			// append the item of that node to the prefix
			String itemset = prefix + " " + node.item;
			// if that node represents a high-utility itemset
			if(node.utility < minUtility_upper&&node.utility >= minUtility_lower) {
				// print it to the console
				System.out.println(itemset + "  #UTIL: " + node.utility);
			}
			// Make a recursive call to print childs of that node
			print_Pre_Large_Itemset(node.childs, itemset);
		}
	}
	/**
	 * Recursive method to print all HUIs stored in the trie to the console.
	 * @param list a list of nodes to explore in a depth-first search way
	 * @param prefix the current prefix, which is the concatenation of all items in the current
	 * branch of the tree.
	 */
	public void print_Large_Itemset(List<Node> list, String prefix) {
		// for each node
		for(Node node : list) {
			// append the item of that node to the prefix
			String itemset = prefix + " " + node.item;
			// if that node represents a high-utility itemset
			if(node.utility >= minUtility_upper) {
				// print it to the console
				System.out.println(itemset + "  #UTIL: " + node.utility);
			}
			// Make a recursive call to print childs of that node
			print_Large_Itemset(node.childs, itemset);
		}
	}
	

	/**
	 * Write HUIs found to a file. Note that this method write all HUIs found until now
	 * and erase the file by doing so, if the file already exists.
	 * @param output the output file path
	 * @throws IOException if error writing to output file
	 */
	public void writeHUIsToFile(String output) throws IOException {
		// writer to write the output file 
		BufferedWriter writer_Large = new BufferedWriter(new FileWriter(output+"_Large"));
		// Make a recursive call to the helper method using childs of the root node.
		writeLargesToFile(singleItemsNodes, "", writer_Large);
		// close the file
		writer_Large.close();
		BufferedWriter writer_Pre_Large = new BufferedWriter(new FileWriter(output+"_Pre_Large"));
		// Make a recursive call to the helper method using childs of the root node.
		writePreLargeIsToFile(singleItemsNodes, "", writer_Pre_Large);
		// close the file
		writer_Pre_Large.close();
	}
	
	/**
	 * Helper method to Write HUIs found to a file (a recursive method)
	 * @param writer writer object to write HUIs to file
	 * @param list a list of nodes to explore in a depth-first search way
	 * @param prefix the current prefix, which is the concatenation of all items in the current
	 * branch of the tree.
	 * @throws IOException  if error writing to output file
	 */
	public void writeLargesToFile(List<Node> list, String prefix, BufferedWriter writer) throws IOException {

		// for each node
		for(Node node : list) {
			// append the item of that node to the prefix
			String itemset = prefix + " " + node.item;
			// if that node represents a high-utility itemset
			if(node.utility > minUtility_upper) {
				// save the itemset representing the current branch to file
				writer.write(itemset + "  #UTIL: " + node.utility + "\n");
			}
			// recursive call to extend this itemset
			writeLargesToFile(node.childs, itemset, writer);
		}
	}
	public void writePreLargeIsToFile(List<Node> list, String prefix, BufferedWriter writer) throws IOException {

		// for each node
		for(Node node : list) {
			// append the item of that node to the prefix
			String itemset = prefix + " " + node.item;
			// if that node represents a high-utility itemset
			if(node.utility < minUtility_upper&&node.utility >= minUtility_lower) {
				// save the itemset representing the current branch to file
				writer.write(itemset + "  #UTIL: " + node.utility + "\n");
			}
			// recursive call to extend this itemset
			writePreLargeIsToFile(node.childs, itemset, writer);
		}
	}
	
	
	/**
	 * Print the HUI-Trie for debugging purpose.
	 */
	public void printTrie() {
		System.out.println("==== trie ====");
		// call a recursive helper method to print the trie in a depth-first search way starting
		// with the childs of the root node.
		printTrie(singleItemsNodes, "");
	}
	
	/**
	 * Recursive method to print the trie to the console
	 * @param list a list of nodes to explore in a depth-first search way
	 * @param indent an indentation consisting of a set of tabulations to indent the branches of the
	 *  tree in the console.
	 */
	public void printTrie(List<Node> list, String indent) {
		// for each node
		for(Node node : list) {
			// append the item 
			String itemset = indent + node.item;
			// print the item with its uility to the console
			System.out.println(itemset + "  (" + node.utility + ")");
			// recursively print all child nodes of that node.
			printTrie(node.childs, indent + "\t");
		}
	}
	
	/**
	 * Remove nodes that are not part of a HUI from a list of child nodes.
	 * @param list the list of child nodes
	 * @return true if at least one of the nodes is part of a HUI
	 */
//	public boolean purgeTrie(List<Node> list) {
////		return true;
//		boolean hasChildInHUI = false;
//		Iterator<Node> iter = list.iterator();
//		while (iter.hasNext()){
//			Node node = iter.next();
//			if(node.utility >= minUtility) {
//				hasChildInHUI = true;
//			}else {
//				boolean nodeHasChildInAHUI = purgeTrie(node.childs);
//				if(nodeHasChildInAHUI == false) {
//					iter.remove();
//				}else {
//					hasChildInHUI = true;
//				}
//			}
//		}
//		return hasChildInHUI;
//	}
	
	
	/**
	 * Insert a HUI in the trie.
	 * @param prefix  the prefix of the HUI
	 * @param lastitem the last item of the HUI
	 * @param utility the utility of the HUI
	 * @param prefixLength The current prefix length
	 */
	public void insertHUIinTrie(int prefix[], int prefixLength, int lastitem, int utility) {
		List<Node> listNodes = singleItemsNodes;
		Node currentNode = null;

		// if more than one item, first add all the prefix
		for (int i = 0; i < prefixLength; i++) {
			int item = prefix[i];
			// find the current item
			currentNode = binarySearchForItem(listNodes, item);
			// if not found
			if(currentNode == null) {
				currentNode = new Node(item);
				listNodes.add(middle,currentNode);
				listNodes = currentNode.childs;
			}else {
				listNodes = currentNode.childs;
			}
		}

		// Now the last item... find it!
		currentNode = binarySearchForItem(listNodes, lastitem);
		// if not found
		if(currentNode == null) {
			currentNode = new Node(lastitem, utility); // with utility
			listNodes.add(middle,currentNode);
			huiCount++;
		}else {
			// if found
			if(currentNode.utility == -1) {
				huiCount++;
			}
			currentNode.utility = utility;
		}
	}
	public boolean UpdateHUIinTrie(List<Integer> prefix, int lastitem, int utility) {
		List<Node> listNodes = singleItemsNodes;
		Node currentNode = null;

		// if more than one item, first add all the prefix
		for (int i = 0; i < prefix.size(); i++) {
			int item = prefix.get(i);
			currentNode = binarySearchForItem(listNodes, item);
			if(currentNode == null) {
				return false;
			}else {
				listNodes = currentNode.childs;
			}
		}
		// Now the last item... find it!
		currentNode = binarySearchForItem(listNodes, lastitem);
		// if not found
		if(currentNode == null) {
			return false;
		}else {
			if(currentNode.utility != -1) {
				currentNode.utility += utility;
				return true;
			}
			return false;
		}
	}

	public void UpdateTree(List<Pair> transaction){
		List<Integer> current = new ArrayList<>();
		dfs(transaction, current, 0, 0, 0);
	}
	public void dfs(List<Pair> transaction, List<Integer> current, int index, int length, int accumulatedUtility) {
		if (length > 0) {
			List<Integer> prefix = current.subList(0,length-1);
			int last = current.getLast();
			boolean update = UpdateHUIinTrie(prefix,last,accumulatedUtility);
			if(update){
				//printTrie();
				//System.out.println("minU: " +accumulatedUtility);
			}else{
				return;
			}
//			if(UpdateHUIinTrie(prefix,last,accumulatedUtility)){
////				printTrie();
////				System.out.println("minU: " +accumulatedUtility);
//			};
		}
		for (int i = index; i < transaction.size(); i++) {
			int currentItem = transaction.get(i).item;
			current.add(currentItem);
			dfs(transaction, current, i + 1, length + 1, accumulatedUtility + transaction.get(i).utility);
			current.remove(current.size() - 1);
		}
	}

	// NOTE : This variable used by the binary search has been made global so that we can insert a new node
	// at the position where it should be in a list of nodes
	int middle = -1;
	
	public Node binarySearchForItem(List<Node> list, int item) {
		middle = 0;
		// perform a binary search to check if the item is here
        int first = 0;
        int last = list.size() - 1;
       
        // the binary search
        while( first <= last )
        {
        	middle = ( first + last ) >>> 1; // divide by 2
            if(compareItemsByRank(item, list.get(middle).item) >0){
            	first = middle + 1;  
            }
            else if(compareItemsByRank(item, list.get(middle).item) <0){
            	last = middle - 1; 
           }
            else{
            	return list.get(middle);
            }
        }
        // THE FOLLOWING LINE IS IMPORTANT TO KNOW WHERE
        // TO INSERT THE ITEM IN THE TRIE WHEN USING THE METHOD
        // insertHUIinTrie(...). If it is removed, nodes
        // in the tree are not inserted in the correct order
        // and the binary search does not work which lead
        // to incorrect result.
        middle = first;
		return null;
	}
	
	// ********************* END OF CODE FOR THE HUI-TRIE ***************************************
	
	/**
	 * Default constructor
	 */
	public AlgoPIHUPM() {
		
	}

	/**
	 * Run the algorithm
	 * @param input the input file path
	 * @param upperThreshold the upper utility threshold
	 * @param lowerThreshold the lower utility threshold
	 * @param firstLine the first line to be read
	 * @param lastLine the last line to be read
	 * @throws IOException exception if error while writing the file
	 */
	/** This is the total utility of all transactions in Incremental Database */
	int totalDBUtility_ID;
	/** This is the total utility of all transactions in Original Database */
	int totalDBUtility_OD;
	/** The minimum utility threshold */
	int minUtility_upper;
	int minUtility_lower;
	public void runAlgorithm(String input,float upperThreshold,float lowerThreshold, int firstLine, int lastLine) throws IOException {
		// reset maximum
		maxMemory =0;
		
		// Reset statistics
		candidateCount = 0;
		huiCount = 0; 
		
		// initialize the buffer for storing the current itemset
		itemsetBuffer = new int[BUFFERS_SIZE];
		
		this.firstLine = firstLine;
		// if first time
		boolean firstTime = (mapItemToUtilityList == null);
		List<List<Pair>> newTrans = new ArrayList<>();
		if(firstTime) {
//			writer = new BufferedWriter(new FileWriter(output));
			listOfUtilityLists = new ArrayList<UtilityList>();
			mapItemToRank =  new HashMap<Integer, Integer>();
			mapItemToUtilityList = new HashMap<Integer, UtilityList>();
			// initialize trie
			singleItemsNodes = new ArrayList<Node>(100);
			
			totalDBUtility_OD = 0;
		}
		startTimestamp = System.currentTimeMillis();

		// create a list to store the utility list of new items so that they can be
		// sorted by TWU order
		List<UtilityList> newItemsUtilityLists = new ArrayList<UtilityList>();

		//  We create a  map to store the TWU of each item
		if(mapItemToTWU == null) {
			mapItemToTWU = new HashMap<Integer, Integer>();
		}

		// We scan the database a first time to calculate the TWU of each item.
		BufferedReader myInput = null;
		String thisLine;
		try {
			int tid=1;
			// prepare the object for reading the file
			myInput = new BufferedReader(new InputStreamReader( new FileInputStream(new File(input))));
			// for each line (transaction) until the end of file
			while ((thisLine = myInput.readLine()) != null && tid <= lastLine) {

				if(tid >= firstLine){
					// if the line is  a comment, is  empty or is a
					// kind of metadata
					if (thisLine.isEmpty() == true ||
							thisLine.charAt(0) == '#' || thisLine.charAt(0) == '%' || thisLine.charAt(0) == '@') {
						continue;
					}
					
					// split the transaction according to the : separator
					String split[] = thisLine.split(":"); 
					// the first part is the list of items
					String items[] = split[0].split(" ");
					String utilities[] = split[2].split(" ");

					// the second part is the transaction utility
					int transactionUtility = Integer.parseInt(split[1]);  
					// for each item, we add the transaction utility to its TWU
					List<Pair> transaction = new ArrayList<>();
					for(int i=0; i <items.length; i++){
						// convert item to integer
						Integer item = Integer.parseInt(items[i]);
						Integer util = Integer.parseInt(utilities[i]);
						Pair pair = new Pair(item,util);
						transaction.add(pair);
						// get the current TWU of that item
						Integer twu = mapItemToTWU.get(item);
						Element element = new Element(tid, util, 0);
						// add the utility of the item in the current transaction to its twu
						if(twu == null) {
							UtilityList uList =  new UtilityList(item);
							uList.addElement(element);
							newItemsUtilityLists.add(uList);
							twu = transactionUtility;
							mapItemToUtilityList.put(item, uList);
						}else {
							twu = twu + transactionUtility;
							UtilityList uLItem = mapItemToUtilityList.get(item);
							uLItem.addElement(element);
						}
						mapItemToTWU.put(item, twu);
					}
					totalDBUtility_ID += transactionUtility;
					newTrans.add(transaction);
				}
				tid++;

			}
		} catch (Exception e) {
			// catches exception if error while reading the input file
			e.printStackTrace();
		}finally {
			if(myInput != null){
				myInput.close();
			}
	    }
		
		
		minUtility_upper =  (int)Math.ceil(((totalDBUtility_ID+totalDBUtility_OD)*upperThreshold));
		minUtility_lower =  (int)Math.ceil(((totalDBUtility_ID+totalDBUtility_OD)*lowerThreshold));

		// Sort the new items by TWU
		Collections.sort(newItemsUtilityLists, new Comparator<UtilityList>(){
			public int compare(UtilityList o1, UtilityList o2) {
				return compareItems(o1.item, o2.item);
			}
		});
		
		// Give a rank to each item w.r.t to previous items
		for(UtilityList list : newItemsUtilityLists){
			mapItemToRank.put(list.item, mapItemToRank.size()+1);
		}
		float reconstruct_Condition = (1-upperThreshold)/(upperThreshold-lowerThreshold)*totalDBUtility_ID;
		System.out.println("reconstruct_Condition: "+reconstruct_Condition);

		if(firstTime||reconstruct_Condition>=totalDBUtility_OD){
			// Add the utility lists of new items to the list of utility lists of all items
			listOfUtilityLists.addAll(newItemsUtilityLists);
			// check the memory usage
			checkMemory();

			// Remove itemsets of size 1 that do not appear in DP
			ArrayList<UtilityList> listULForRecursion = new ArrayList<UtilityList>(listOfUtilityLists.size());
			for(UtilityList ul: listOfUtilityLists) {
				// we keep only utility lists of items in DP
//			if(ul.sumIutilsDP != 0) {
//				listULForRecursion.add(ul);
//			}
				if (mapItemToTWU.get(ul.item)>minUtility_lower) {
					listULForRecursion.add(ul);
				}
			}
			listULForRecursion.sort(new Comparator<UtilityList>(){
				@Override
				public int compare(UtilityList o1, UtilityList o2) {
					return compareItemsByRank(o1.item,o2.item);
				}
			});
			int arrayRu[] = new int[lastLine + 1];
			for (int i = listULForRecursion.size() - 1; i >= 0; i--) {
				UtilityList ul = listULForRecursion.get(i);
				int newRemain = 0;
				for (int j = 0; j < ul.elements.size(); j++) {
					Element element = ul.elements.get(j);
					element.rutils = arrayRu[element.tid];
					arrayRu[element.tid] += element.iutils;
					newRemain += element.rutils;
				}
				ul.sumRutils = newRemain;
			}
			incFHM(itemsetBuffer, 0, null, listULForRecursion);
			totalDBUtility_OD+=totalDBUtility_ID;
			totalDBUtility_ID =0;
			System.out.println("Remine");
		}else{
			for(List<Pair> transaction:newTrans){
				transaction.sort((o1, o2) -> compareItemsByRank(o1.item, o2.item));
				UpdateTree(transaction);
			}
			System.out.println("Update");
		}


//		if(!firstTime){
//			purgeTrie(singleItemsNodes);
//		}
		
		// check the memory usage again and close the file.
		checkMemory();
		
		//closeFile();
//		writer.close();
		// record end time
		endTimestamp = System.currentTimeMillis();
		
		totalTimeForAllRuns += (endTimestamp - startTimestamp);
		totalCandidateCountForAllRuns += candidateCount;
//		totalHUIForAllRuns += huiCount;
	}
	
	/**
	 * This is the recursive method to find all high utility itemsets. It writes
	 * the itemsets to the output file.
	 * @param prefix  This is the current prefix. Initially, it is empty.
	 * @param pUL This is the Utility List of the prefix. Initially, it is empty.
	 * @param ULs The utility lists corresponding to each extension of the prefix.
	 * @param prefixLength The current prefix length
	 * @throws IOException
	 */
	private void incFHM(int [] prefix, int prefixLength, UtilityList pUL, List<UtilityList> ULs)
			throws IOException {
		
		// For each extension X of prefix P
 		for(int i=0; i< ULs.size(); i++){
			UtilityList X = ULs.get(i);
			// If X does not appear in DP, then we can skip it
//			if(X.sumIutilsDP == 0) {
////				System.out.println("TEST");
//				continue;
//			}

			// If pX is a high utility itemset.
			// we save the itemset:  pX 
			int utilityOfX = X.sumIutils;
			if(utilityOfX >= minUtility_lower){
				// save to file
				insertHUIinTrie(prefix, prefixLength, X.item, utilityOfX);
			}
			
			// If the sum of the remaining utilities for pX
			// is higher than minUtility, we explore extensions of pX.
			// (this is the pruning condition)
			if(X.sumIutils + X.sumRutils >= minUtility_lower){
				// This list will contain the utility lists of pX extensions.
				List<UtilityList> exULs = new ArrayList<UtilityList>();
				// For each extension of p appearing
				// after X according to the ascending order
				for(int j=i+1; j < ULs.size(); j++){
					UtilityList Y = ULs.get(j);
					
//					// If Y does not appear in DP, then we can skip it
					if(Y.sumIutils == 0) {
						continue;
					}
					candidateCount++;
					// =========================== END OF NEW OPTIMIZATION
					
					// we construct the extension pXY 
					// and add it to the list of extensions of pX
					UtilityList temp = construct(pUL, X, Y);
					if(temp != null) {
						exULs.add(temp);
					}
				}
				// We create new prefix pX
				itemsetBuffer[prefixLength] = X.item;
				
				// We make a recursive call to discover all itemsets with the prefix pXY
				incFHM(itemsetBuffer, prefixLength+1, X, exULs); 
			}
		}
	}

	/**
	 * Method to compare items by their TWU
	 * @param item1 an item
	 * @param item2 another item
	 * @return 0 if the same item, >0 if item1 is larger than item2,  <0 otherwise
	 */
	private int compareItems(int item1, int item2) {
		int compare = mapItemToTWU.get(item1) - mapItemToTWU.get(item2);
		// if the same, use the lexical order otherwise use the TWU
		//*************** BEGIN NEW ****************************
		//  DESACTIVATE THE TWU SORTING ORDER HERE
		// ***************************************************
		return (compare == 0)? item1 - item2 :  compare;
	}
	
	private int compareItemsByRank(int item1, int item2) {
		int compare = mapItemToRank.get(item1) - mapItemToRank.get(item2);
		// if the same, use the lexical order otherwise use the TWU
		//*************** BEGIN NEW ****************************
		//  DESACTIVATE THE TWU SORTING ORDER HERE
		// ***************************************************
		return (compare == 0)? item1 - item2 :  compare;
	}
	
	
	/**
	 * This method constructs the utility list of pXY
	 * @param P :  the utility list of prefix P.
	 * @param px : the utility list of pX
	 * @param py : the utility list of pY
	 * @return the utility list of pXY
	 */
	private UtilityList construct(UtilityList P, UtilityList px, UtilityList py) {
		
		//== new optimization - LA-prune  == /
		// Initialize the sum of total utility
		long totalUtility = px.sumIutils + px.sumRutils;
		
		// create an empy utility list for pXY
		UtilityList pxyUL = new UtilityList(py.item);
		
		// FIRST TREAT ALL ELEMENTS OF DP IN REVERSE ORDER
		for (int i = px.elements.size() - 1; i >= 0; i--) {
			Element ex = px.elements.get(i);

			// do a binary search to find element ey in py with tid = ex.tid
			Element ey = findElementWithTID(py.elements, ex.tid);
			if(ey == null){
				totalUtility -= (ex.iutils+ex.rutils);
				if(totalUtility < minUtility_lower) {
					return null;
				}
				continue;
			}
			// if the prefix p is null
			if(P == null){
				// Create the new element
				Element eXY = new Element(ex.tid, ex.iutils + ey.iutils, ey.rutils);
				// add the new element to the utility list of pXY
				pxyUL.addElement(eXY);
				
			}else{
				// find the element in the utility list of p wih the same tid
				Element e = findElementWithTID(P.elements, ex.tid);
				if(e != null){
					// Create new element
					Element eXY = new Element(ex.tid, ex.iutils + ey.iutils - e.iutils,
								ey.rutils);
					// add the new element to the utility list of pXY
					pxyUL.addElement(eXY);
				}
			}	
		}
		
		// PRUNING: IF THERE IS NO ELEMENT IN DP, WE DON'T NEED TO CONTINUE
		// CONSTRUCTING THE UTILITY LIST
		if(pxyUL.elements.size() == 0) {
			return null;
		}
		pxyUL.elements= pxyUL.elements.reversed();
		return pxyUL;
	}
	
	/**
	 * Do a binary search to find the element with a given tid in a utility list
	 * @param list the utility list
	 * @param tid  the tid
	 * @return  the element or null if none has the tid.
	 */
	private Element findElementWithTID(List<Element> list, int tid){
		// perform a binary search to check if  the subset appears in  level k-1.
        int first = 0;
        int last = list.size() - 1;
       
        // the binary search
        while( first <= last )
        {
        	int middle = ( first + last ) >>> 1; // divide by 2

            if(list.get(middle).tid < tid){
            	first = middle + 1;  //  the itemset compared is larger than the subset according to the lexical order
            }
            else if(list.get(middle).tid > tid){
            	last = middle - 1; //  the itemset compared is smaller than the subset  is smaller according to the lexical order
            }
            else{
            	return list.get(middle);
            }
        }
		return null;
	}

	
	/**
	 * Method to check the memory usage and keep the maximum memory usage.
	 */
	private void checkMemory() {
		// get the current memory usage
		double currentMemory = (Runtime.getRuntime().totalMemory() -  Runtime.getRuntime().freeMemory())
				/ 1024d / 1024d;
		// if higher than the maximum until now
		if (currentMemory > maxMemory) {
			// replace the maximum with the current memory usage
			maxMemory = currentMemory;
		}
	}
	
	/**
	 * Print statistics about the latest execution to System.out.
	 * @throws IOException 
	 */
	public void printStats() throws IOException {
		System.out.println("=============  EIHI ALGORITHM - SPMF 0.97e - STATS =============");
		System.out.println(" Number of transactions processed " + transactionCount);
		System.out.println(" Execution time ~ "                  + (endTimestamp - startTimestamp) + " ms");
		System.out.println(" Memory ~ "                      + maxMemory+ " MB");
		System.out.println(" New High-utility itemsets found : " + huiCount); 
		System.out.println(" Total high-utility itemsets count : " + getRealHUICount().Large+" Large and "+getRealHUICount().Pre_lage+" Pre_Large");
		System.out.println(" Candidate count : "             + candidateCount);
		System.out.println(" minutil_upper : " + minUtility_upper);
		System.out.println(" minutil_lower : " + minUtility_lower);
		System.out.println("===================================================");
		System.out.println("TOTAL DB Utility: " + (totalDBUtility_OD+totalDBUtility_ID));
		System.out.println("TOTAL CANDIDATEs FOR ALL RUNS:" + totalCandidateCountForAllRuns + " candidates");
//		System.out.println("TOTAL REAL HUIs: " + totalHUIForAllRuns);
		System.out.println("TOTAL TIME FOR ALL RUNS: " + totalTimeForAllRuns + " ms");
		System.out.println("===================================================");
	}



}