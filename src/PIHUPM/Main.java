package PIHUPM;

import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;
import java.io.UnsupportedEncodingException;
import java.net.URL;


/**
 * Example of how to use the EIHI algorithm from the source code by processing a single file
 * in several parts (updates).
 * 
 * @author Philippe Fournier-Viger, 2014
 */
public class Main {

	public static void main(String[] arg) throws IOException {

		String input = "mushroom.txt";  // retails_utilityPFV
		float upperThreshold = 0.18f;
		float lowerThreshold = 0.15f;
		// the number of updates to be performed
		int numberOfUpdates = 9;

		// scan the database to count the number of lines
		// for our test purpose
		int linecount = countLines(input);
		int firstLine = 0;
		int lastLine = firstLine + (int) (linecount * 0.9f);
		double addedratio = 0.1d / ((double) numberOfUpdates);
		int linesForeEachUpdate = (int)(addedratio * linecount);
		// Apply the algorithm several times
		AlgoPIHUPM algo = new AlgoPIHUPM();
		for(int i = 0; i < numberOfUpdates; i++){
			if(i == numberOfUpdates -1) {
				System.out.println("" + i + ") Run the algorithm using line " + firstLine + " to line " + linecount + " of the input database.");
				algo.runAlgorithm(input, upperThreshold,lowerThreshold, firstLine, linecount);
				algo.printStats();
				System.out.println("NUMBER OF LARGE ITEMSET FOUND: " + algo.getRealHUICount().Large);
				System.out.println("NUMBER OF PRE_LARGE ITEMSET FOUND: " + algo.getRealHUICount().Pre_lage);
				// PRINT THE HUIs FOUND
				//algo.printHUIs();
				//algo.printTrie();

			}else {
				// If this is not the last update
				System.out.println("" + i + ") Run the algorithm using line " + firstLine + " to line " + lastLine + " of the input database.");
				algo.runAlgorithm(input, upperThreshold,lowerThreshold, firstLine, lastLine);
				algo.printStats();
				System.out.println("NUMBER OF LARGE ITEMSET FOUND: " + algo.getRealHUICount().Large);
				System.out.println("NUMBER OF PRE_LARGE ITEMSET FOUND: " + algo.getRealHUICount().Pre_lage);
				// PRINT THE HUIs FOUND
				//algo.printHUIs();
				//algo.printTrie();
			}
			//algo.printStats();
			
			firstLine = lastLine+1;
			lastLine = firstLine + linesForeEachUpdate;
		}
		
		// Print the number of HUIs found until now to the console
		System.out.println("NUMBER OF LARGE ITEMSET FOUND: " + algo.getRealHUICount().Large);
		System.out.println("NUMBER OF PRe_LARGE ITEMSET FOUND: " + algo.getRealHUICount().Pre_lage);
		
		// PRINT THE HUIs FOUND
		algo.printHUIs();
		
		// PRINT THE TRIE FOR DEBUGGING
		//algo.printTrie();
		
		// WE CAN ALSO WRITE ALL THE HUIs found until now to a file at any time with
		// the following code
		String output = ".//output.txt";
		algo.writeHUIsToFile(output);
	}

	/**
	 * This methods counts the number of lines in a text file.
	 * @param filepath the path to the file
	 * @return the number of lines as an int
	 * @throws IOException Exception if error reading/writting file
	 */
	public static int countLines(String filepath) throws IOException {
		LineNumberReader reader = new LineNumberReader(new FileReader(filepath));
		while(reader.readLine() != null) {}
		int count = reader.getLineNumber();
		reader.close();
		return count;
	}

	public static String fileToPath(String filename)
			throws UnsupportedEncodingException {
		URL url = Main.class.getResource(filename);
		return java.net.URLDecoder.decode(url.getPath(), "UTF-8");
	}
}
