/**
 * @author tnaessens
 */

import java.util.Arrays;

public class GreedyPartitionSolver implements PartitionSolver {

	private int[] schotten;
	private int gemiddelde;
	private int som;
	private int totaal;
	private int j;

	public int[] solve(int[] row, int k) {
		
		if (k > row.length) {
			throw new IllegalArgumentException();
		}

		schotten = new int[k - 1];

		// Berekent het eerste gemiddelde
		gemiddelde = getGemiddelde(row, k);
		// Overloopt de rij en kijkt telkens als de totaalsom van de huidige elementen in de partitie
		// Als de som overschreden wordt, wordt een schotje geplaatst en wordt een nieuw gemiddelde berekent
		for (int i = 0; i < row.length; i++) {
			totaal += row[i];
			if (totaal > gemiddelde || k - j - 1 == row.length - i) {
				totaal = 0;
				if (i == 0) {
					schotten[j] = i + 1;
				} else {
					schotten[j] = i;
				}
				j++;
				gemiddelde = getGemiddelde(Arrays.copyOfRange(row, i + 1, row.length), k - j);
			}
		}
		return schotten;
	}
	
	// Functie die het gemiddelde van de opgegeven deelrij berekent
	private int getGemiddelde(int[] row, int k) {
		som = 0;
		for (int i = 0; i < row.length; i++) {
			som += row[i];
		}
		return som / k;
	}

	
}
