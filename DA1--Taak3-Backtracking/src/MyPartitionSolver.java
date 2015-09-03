
/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
public class MyPartitionSolver implements PartitionSolver {

	int[] row;
	int k;
	int[][] table;

	public int[] solve(int[] row, int k) {

		int[] p = new int[row.length];

		p[0] = row[0];
		for(int i = 1; i < row.length; i++) {
			p[i] = p[i-1] + row[i];
		}

		int[][] M = new int[k][row.length];
		int[][] d = new int[k][row.length];

		for(int i = 0; i < row.length; i++) {
			M[0][i] = p[i];
		}
		
		for(int i = 0; i < k; i++) {
			M[i][0] = i+1;
		}

		for(int i = 1; i < k; i++) {
			for(int j = 1; j < row.length; j++) {
				M[i][j] = Integer.MAX_VALUE;;
				for(int x = 0; x < i; x++) {
					int s = Math.max(M[x][j], p[i]-p[x]);
					if(M[i][j] > s) {
						M[i][j] = s;
						d[i][j] = x;
					}
				}

			}
		}

		return null;

	}

	public void makeTable(int[] row, int k) {

	}

	public void write(int[] row, int[] result) {
		boolean found = false;
		for (int i = 0; i < row.length; i++) {
			System.out.print(row[i]);
			for (int j = 0; j < result.length; j++) {
				if (result[j] == i + 1) {
					found = true;
				}
			}
			if (found) {
				System.out.print(" |");
				found = false;
			}
			System.out.print(" ");
		}
		System.out.println("");
	}
}
