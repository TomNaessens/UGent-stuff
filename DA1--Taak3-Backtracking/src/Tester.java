

/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
public class Tester {

//	private static int[] row = {1,1,1,1,1,1,1,1,1};
//	private static int[] row = {3, 7, 2, 5, 4, 9 ,7 ,8 ,5 ,2};
//	private static int[] row = {1, 7, 3, 4, 8, 1, 2, 4, 5, 6};
	private static int[] row = {1, 2, 3, 4, 5, 6, 7, 8, 9};
//	private static int[] row = {1, 2, 3, 4, 5, 6};
//	private static int[] row = {500, 800, 600, 400, 800, 100, 900, 250, 400, 300};
//	private static int[] row = {9, 8, 7, 6, 5, 4, 3, 2, 1};
//	private static int[] row = {4, 7, 3, 6, 8, 9};
//	private static int[] row = {1, 1, 1, 1, 1, 1, 1, 1000, 1000};
//	private static int[] row = {10, 30, 30, 40};
//	private static int[] row = {100, 200, 200, 300};
//	private static int[] row = {10000,1,1,1,1,1,1,1,1,1};
	private static int k = 3;

	public static void main(String[] args) {
		GreedyPartitionSolver gps = new GreedyPartitionSolver();
		int[] result = gps.solve(row, k);
//		boolean found = false;
//
		for (int i = 0; i < result.length; i++) {
			System.out.print(result[i] + " ");
		}
		System.out.println("");
//
//		for (int i = 0; i < row.length; i++) {
//			System.out.print(row[i]);
//			for (int j = 0; j < result.length; j++) {
//				if (result[j] == i + 1) {
//					found = true;
//				}
//			}
//			if (found) {
//				System.out.print(" |");
//				found = false;
//			}
//			System.out.print(" ");
//		}
//		System.out.println("");
	}
}
