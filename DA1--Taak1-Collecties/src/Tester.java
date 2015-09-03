/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */


/**
 *
 * @author tnaessens
 */
public class Tester {

	/**
	 * @param args the command line arguments
	 */
	private static int aantal;

	public static void main(String[] args) {
		OldestPeopleFinder klasse;
		int i = 0;

		while (i <= 3000000) {
			System.out.print("Input:\t" + i + "\tMs:\t");

			for (int j = 0; j < 10; j++) {
				//klasse = new MyOldestPeopleFinder(i);
				klasse = null;
				System.gc();
				System.out.print("\t");
			}
			System.out.println("");

			i += 50000;
		}

	}
}
