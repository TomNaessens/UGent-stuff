/**
 * @author Tom Naessens
 */
public class BacktrackingPartitionSolver implements PartitionSolver {

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

		// Initialiseren van sums array
		System.arraycopy(row, 0, tempSums, 0, result.length);
		for (int i = result.length; i < row.length; i++) {
			tempSums[tempSums.length - 1] += row[i];
		}
		sums = tempSums.clone(); // Als we niet klonen heeft Java de neiging er hetzelfde object van te maken

		minDif = getVerschil(sums); // Initialisatie van het kleinste verschil

		recursive(row, result, 0);

		return result;
	}

	public void recursive(int[] row, int[] tempResult, int startIndex) {

		// Berekent van de 'speciale configuratie' waarvan het eerste schotje op index startIndex 
		// staat de sum, en steekt dit in een tijdelijke somarray om daarop de nieuwe bewerkingen door te voeren
		for (int i = 0; i < tempResult.length; i++) {
			tempResult[i] = startIndex + 1 + i;

			if (startIndex != 0) { // Aangezien we de som hiervoor al hebben opgemaakt
				tempSums[i] += row[startIndex + i];
				tempSums[i + 1] -= row[startIndex + i];
			}

		}
		sums = tempSums.clone(); // Als we niet klonen heeft Java de neiging er hetzelfde object van te maken
		
		// Als het verschil kleiner is, onthoudt dit, maar probeer betere configuraties te zoeken
		if (getVerschil(sums) < minDif) {
			minDif = getVerschil(sums);
			result = tempResult.clone();
		}

		// Zet het laatste schotje naar achter, tot het niet verder kan en verschuift dan schotje ervoor
		// Als het verschil groter wordt, springen we een niveau omhoog (=backtracking).
		int toMove = 1;
		while (toMove < tempResult.length) {

			while (tempResult[tempResult.length - toMove] < row.length - toMove) {
				tempResult[tempResult.length - toMove] += 1;

				sums[tempResult.length - toMove] += row[tempResult[tempResult.length - toMove] - 1];
				sums[tempResult.length - toMove + 1] -= row[tempResult[tempResult.length - toMove] - 1];

				if (getVerschil(sums) < minDif) {
					minDif = getVerschil(sums);
					result = tempResult.clone();
					recursive(row, tempResult, startIndex + 1); // Backtracking
				}

			}

			toMove++;
		}

		if (startIndex < row.length - tempResult.length - 1) {
			recursive(row, tempResult, startIndex + 1);
		}

	}

	// Methode die het verschil berekent tussen de grootste en kleinste som van de elementen van de partities
	public int getVerschil(int[] sums) {
		int grootste = Integer.MIN_VALUE;
		int kleinste = Integer.MAX_VALUE;
		for (int i = 0; i < sums.length; i++) {
			kleinste = Math.min(kleinste, sums[i]);
			grootste = Math.max(grootste, sums[i]);
		}
		return grootste - kleinste;
	}
}
