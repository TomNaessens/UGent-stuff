
/**
 *
 * @author tnaessens
 * 
 */
public class MyLTiles implements LTiles {

	private int[][] grid;
	private int teller;
	private int kwadrant; //0 = linksboven, 1 = rechtsboven, 2 = rechtsonder, 3 = linksonder

	public int[][] tile(int k, int row, int col) {
		
			teller = 0; // initialiseert de teller op 0

			int n = (int) (Math.pow(2, k)); // Berekent de dimensie van de tabel

			if(k < 0 || row > n-1 || col > n-1) { // Bij een onverwachte (foute) invoer geven we een lege array terug
				return new int[0][0];
			}

			grid = new int[n][n]; // Maakt een grid aan
			grid[row][col] = -1; // Zet het zwarte hokje op de juiste plaats

			verdeelGrid(k, row, col, 0, 0);



		return grid;
	}

	/*
	 * Dit is de recursieve methode. Hij deelt het venster steeds opnieuw en opnieuw op
	 * Parameters:
	 * k - macht van 2, geeft de grootte van het kader aan
	 * row - rij van het -1 vakje of het blokje dat net getekend is ten opzichte van het volledige
	 * grid dat overeenkomt met de linkerbovenhoek van het kader waarin gewerkt wordt
	 * col - kolom van het -1 vakje of het blokje dat net getekend is ten opzichte van het volledige
	 * grid dat overeenkomt met de linkerbovenhoek van het kader waarin gewerkt wordt
	 * grow - "grid-row": rijnummer ten opzichte van het volledige grid dat overeenkomt met de linkerbovenhoek
	 *		  van het kader waarin gewerkt wordt
	 * gcol - "grid-column": kolomnummer ten opzichte van het volledige grid dat overeenkomt met de linkerbovenhoek
	 *		  van het kader waarin gewerkt wordt
	 */
	public void verdeelGrid(int k, int row, int col, int grow, int gcol) {
		int mp = (int) (Math.pow(2, k) / 2) - 1; // mp - middelpunt tov van het nieuwe grid

		if (k > 0) { // Teken een rechthoekje als het het deel van het grid groter is dan of gelijk is aan 2*2
			if (row > mp + grow) {
				if (col > mp + gcol) { // -1 rechtsonder
					kwadrant = 2;
				} else {		 // -1 linksonder
					kwadrant = 3;
				}
			} else {
				if (col > mp + gcol) { // -1 rechtsboven
					kwadrant = 1;
				} else {		 // -1 linksboven
					kwadrant = 0;
				}
			}
			drawTile(mp + grow, mp + gcol, kwadrant);
			if (k > 1) {
				if (kwadrant == 0) {
					verdeelGrid(k - 1, row, col, grow, gcol);
					verdeelGrid(k - 1, mp + 1 + grow, gcol, grow, mp + 1 + gcol);
					verdeelGrid(k - 1, grow, mp + 1 + gcol, mp + 1 + grow, gcol);
					verdeelGrid(k - 1, grow, gcol, mp + 1 + grow, mp + 1 + gcol);
				} else if (kwadrant == 1) {
					verdeelGrid(k - 1, mp + grow, mp + gcol, grow, gcol);
					verdeelGrid(k - 1, row, col, grow, mp + 1 + gcol);
					verdeelGrid(k - 1, grow, mp + 1 + gcol, mp + 1 + grow, gcol);
					verdeelGrid(k - 1, grow, gcol, mp + 1 + grow, mp + 1 + gcol);
				} else if (kwadrant == 2) {
					verdeelGrid(k - 1, mp + grow, mp + gcol, grow, gcol);
					verdeelGrid(k - 1, mp + 1 + grow, gcol, grow, mp + 1 + gcol);
					verdeelGrid(k - 1, grow, mp + 1 + gcol, mp + 1 + grow, gcol);
					verdeelGrid(k - 1, row, col, mp + 1 + grow, mp + 1 + gcol);
				} else if (kwadrant == 3) {
					verdeelGrid(k - 1, mp + grow, mp + gcol, grow, gcol);
					verdeelGrid(k - 1, mp + 1 + grow, gcol, grow, mp + 1 + gcol);
					verdeelGrid(k - 1, row, col, mp + 1 + grow, gcol);
					verdeelGrid(k - 1, grow, gcol, mp + 1 + grow, mp + 1 + gcol);
				}
			}
		}



	}

	/*
	 * Tekent een tegel, argumenten row, col van 'startpositie', en de orientatie
	 * Orientatie:
	 * 0 - opening naar linksboven
	 * 1 - opening naar rechtsboven
	 * 2 - opening naar rechtsonder
	 * 3 - opening naar linksonder
	 */
	public void drawTile(int row, int col, int or) {
		if (or == 0) {
			grid[row][col + 1] = teller;
			grid[row + 1][col + 1] = teller;
			grid[row + 1][col] = teller;
		} else if (or == 1) {
			grid[row][col] = teller;
			grid[row + 1][col + 1] = teller;
			grid[row + 1][col] = teller;
		} else if (or == 2) {
			grid[row][col] = teller;
			grid[row][col + 1] = teller;
			grid[row + 1][col] = teller;
		} else if (or == 3) {
			grid[row][col] = teller;
			grid[row][col + 1] = teller;
			grid[row + 1][col + 1] = teller;
		}
		teller++;
	}
}
