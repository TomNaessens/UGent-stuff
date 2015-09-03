
import java.awt.Dimension;
import java.util.Random;
import javax.swing.JFrame;

/**
 *
 * @author tnaessens
 */
public class MyLTiles implements LTiles {

	/**
	 * @param args the command line arguments
	 */
	private int[][] grid;
	private int teller;
	private Random rd = new Random();

	public int[][] tile(int k, int row, int col) {
		teller = 0; // initialiseert de teller op 0

		int n = (int) (Math.pow(2, k)); // Berekent de dimensie van de tabel
		grid = new int[n][n];
		grid[row][col] = -1;

		//long tijd = System.currentTimeMillis();
		verdeelGrid(k, row, col, 0, 0);
		//System.out.println(System.currentTimeMillis() - tijd);

		//printGrid();

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
	 * grow - rijnummer ten opzichte van het volledige grid dat overeenkomt met de linkerbovenhoek
	 *		  van het kader waarin gewerkt wordt
	 * gcol - kolomnummer ten opzichte van het volledige grid dat overeenkomt met de linkerbovenhoek
	 *		  van het kader waarin gewerkt wordt
	 */
	public void verdeelGrid(int k, int row, int col, int grow, int gcol) {
		if (k != 0) {
			int mp = (int) (Math.pow(2, k) / 2) - 1; // mp - middelpunt tov van het nieuwe grid

			if (row > mp + grow) {
				if (col > mp + gcol) { // -1 rechtsonder

					drawTile(mp + grow, mp + gcol, 2);

					verdeelGrid(k - 1, mp + grow, mp + gcol, grow, gcol);
					verdeelGrid(k - 1, mp + 1 + grow, gcol, grow, mp + 1 + gcol);
					verdeelGrid(k - 1, grow, mp + 1 + gcol, mp + 1 + grow, gcol);
					verdeelGrid(k - 1, row, col, mp + 1 + grow, mp + 1 + gcol);

				} else {		 // -1 linksonder
					drawTile(mp + grow, mp + gcol, 3);

					verdeelGrid(k - 1, mp + grow, mp + gcol, grow, gcol);
					verdeelGrid(k - 1, mp + 1 + grow, gcol, grow, mp + 1 + gcol);
					verdeelGrid(k - 1, row, col, mp + 1 + grow, gcol);
					verdeelGrid(k - 1, grow, gcol, mp + 1 + grow, mp + 1 + gcol);

				}
			} else {
				if (col > mp + gcol) { // -1 rechtsboven
					drawTile(mp + grow, mp + gcol, 1);

					verdeelGrid(k - 1, mp + grow, mp + gcol, grow, gcol);
					verdeelGrid(k - 1, row, col, grow, mp + 1 + gcol);
					verdeelGrid(k - 1, grow, mp + 1 + gcol, mp + 1 + grow, gcol);
					verdeelGrid(k - 1, grow, gcol, mp + 1 + grow, mp + 1 + gcol);

				} else {		 // -1 linksboven
					drawTile(mp + grow, mp + gcol, 0);

					verdeelGrid(k - 1, row, col, grow, gcol);
					verdeelGrid(k - 1, mp + 1 + grow, gcol, grow, mp + 1 + gcol);
					verdeelGrid(k - 1, grow, mp + 1 + gcol, mp + 1 + grow, gcol);
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

	/*public void printGrid() {
		for (int i = 0; i < grid.length; i++) {
			for (int j = 0; j < grid[i].length; j++) {
				System.out.print(grid[i][j] + " ");
			}
			System.out.println("");
		}
	}*/
}
