package Pre_TK_INC_2;


import java.io.FileReader;
import java.io.IOException;
import java.io.LineNumberReader;

public class MainBaseLineIEEE {

	public static void main(String[] arg) throws IOException {

		String input ="chainstore.txt";
		String output = "output.txt";
		int upper_k = 500;
		int lower_k = 50;
		for (int l = 0; l < 5; l++) {
			System.out.println("upper_k: "+upper_k);
			System.out.println("lower_k: "+lower_k);
			// the number of updates to be performed
			int numberOfUpdates = 10;

			// scan the database to count the number of lines
			// for our test purpose
			int linecount = countLines(input);
			int firstLine = 0;// ;
			int lastLine = firstLine + (int) (linecount * 0.99f);
			double addedratio = 0.01d / ((double) numberOfUpdates);
			int linesForeEachUpdate = (int) (addedratio * linecount);

			System.gc();
			// Apply the algorithm several times
			AlgoTKINC algo = new AlgoTKINC();
			for (int i = 0; i < numberOfUpdates+1; i++) {
				// Applying the algorithm
				// If this is the last update, we make sure to run until the last line
				if (i == numberOfUpdates) {
					System.out.println("" + (i+1) + ") Run the algorithm using line " + firstLine + " to before line "
							+ linecount + " of the input database.");
					algo.runAlgorithm(input, output,true, lower_k,upper_k, firstLine, linecount);
				} else {
					// If this is not the last update
					System.out.println("" + (i+1) + ") Run the algorithm using line " + firstLine + " to before line "
							+ lastLine + " of the input database.");
					algo.runAlgorithm(input, output, true,lower_k,upper_k, firstLine, lastLine);
				}
				algo.printStats();

				firstLine = lastLine;
				lastLine = firstLine+linesForeEachUpdate;

			}
			upper_k -= 1000;
			lower_k -= 10;

		}
	}

	/**
	 * This methods counts the number of lines in a text file.
	 * 
	 * @param filepath the path to the file
	 * @return the number of lines as an int
	 * @throws IOException Exception if error reading/writting file
	 */
	public static int countLines(String filepath) throws IOException {
		LineNumberReader reader = new LineNumberReader(new FileReader(filepath));
		while (reader.readLine() != null) {
		}
		int count = reader.getLineNumber();
		reader.close();
		return count;
	}

}
