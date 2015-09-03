/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

/**
 *
 * @author tnaessens
 */
public class temp implements PartitionSolver {

	int[] result; // Houdt het optimale resultaat bij
	int[] tempResult;
	int[] sums; // Houdt de som van elke deelrij bij zodanig dat dit niet steeds opnieuw moet berekent worden
	int[] tempSums;
	int minDif; // Houdt het kleinste verschil tussen de grootste en de kleinste rij bij

	public int[] solve(int[] row, int k) {
		sums = new int[k];
		tempSums = new int[k];
		result = new int[k - 1];
		tempResult = new int[k - 1];
		System.arraycopy(row, 0, tempSums, 0, result.length);
		for (int i = result.length; i < row.length; i++) {
			tempSums[tempSums.length - 1] += row[i];
		}
		sums = tempSums.clone(); // Als we niet klonen heeft Java de neiging er hetzelfde object van te maken

		minDif = getVerschil(sums);

		recursive(row, result, 0);

//		System.out.println(minDif);
//		write(row, result);

		return result;
	}

	public void recursive(int[] row, int[] tempResult, int startIndex) {

		for (int i = 0; i < tempResult.length; i++) {
			tempResult[i] = startIndex + 1 + i;

			if (startIndex != 0) { // Aangezien we de som hiervoor al hebben opgemaakt
				tempSums[i] += row[startIndex + i];
				tempSums[i + 1] -= row[startIndex + i];
			}

		}
		sums = tempSums.clone(); // Als we niet klonen heeft Java de neiging er hetzelfde object van te maken

//		System.out.print(getVerschil(sums) + " || ");

//		write(row, tempResult);

		int toMove = 1;
		while (toMove < tempResult.length) {

			while (tempResult[tempResult.length - toMove] < row.length - toMove) {
				tempResult[tempResult.length - toMove] += 1;

				sums[tempResult.length - toMove] += row[tempResult[tempResult.length - toMove] - 1];
				sums[tempResult.length - toMove + 1] -= row[tempResult[tempResult.length - toMove] - 1];

//				System.out.print(getVerschil(sums) + " || ");
//				write(row, tempResult);

				if (getVerschil(sums) < minDif) {
					minDif = getVerschil(sums);
					result = tempResult.clone();
					recursive(row, tempResult, startIndex + 1);
				}

			}

			toMove++;
		}

		if (startIndex < row.length - tempResult.length - 1) {
			recursive(row, tempResult, startIndex + 1);
		}

	}

	public int getVerschil(int[] sums) {
		int grootste = Integer.MIN_VALUE;
		int kleinste = Integer.MAX_VALUE;
		for (int i = 0; i < sums.length; i++) {
			kleinste = Math.min(kleinste, sums[i]);
			grootste = Math.max(grootste, sums[i]);
		}
		return grootste - kleinste;
	}

//	public void write(int[] row, int[] result) {
//		boolean found = false;
//		for (int i = 0; i < row.length; i++) {
//			System.out.print(row[i]);
//			for (int j = 0; j < result.length; j++) {
//				if (result[j] == i + 1) {
//					found = true;
//				}
//			}
//			if (found) {
//				System.out.print("|");
//				found = false;
//			} else {
//				System.out.print(" ");
//			}
//		}
//		System.out.println("");
//	}
}
