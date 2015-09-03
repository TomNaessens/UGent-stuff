public interface LTiles {

	/**
	 * Verdeelt een vierkant met zijde 2^k in L-tegels. Het lege vakje bevindt
	 * zich op rij row en kolom col (geteld vanaf 0) en mag niet bedekt worden
	 * door een tegel. Retourneert een tabel met daarin de verdeling zoals
	 * aangegeven in de opgave.
	 * 
	 * @param k
	 *            geeft de lengte 2^k van de zijde van het vierkant aan
	 * @param row
	 *            rij waarop het lege vakje zich bevindt
	 * @param col
	 *            kolom waarop het lege vakje zich bevindt
	 * @return tabel met de verdeling.
	 */
	int[][] tile(int k, int row, int col);

}