import java.awt.Dimension;
import java.awt.Graphics;

import javax.swing.JPanel;

/**
 * Visualizes the result of the Tile method of the LTiles interface.
 * 
 * @author Bart Mesuere
 * 
 */
public class TilePanel extends JPanel {

	private static final long serialVersionUID = 6169030729846472019L;

	// the grid to visualize
	private final int[][] grid;

	public TilePanel(int[][] grid) {
		this.grid = grid;
		setPreferredSize(new Dimension(100, 100));
	}

	/**
	 * This is not the most efficient way to draw the grid ;)
	 */
	@Override
	public void paintComponent(Graphics g) {
		int tileSize = (int) Math.floor((Math.min(getHeight(), getWidth()) - 1.0) / grid.length);

		// draw the outline of the grid
		g.drawRect(0, 0, tileSize * grid.length + 1, tileSize * grid.length + 1);

		// draw vertical lines
		for (int row = 0; row < grid.length; row++) {
			int prev = grid[row][0];
			for (int col = 1; col < grid.length; col++) {
				if (prev != grid[row][col])
					g.drawLine(col * tileSize, row * tileSize, col * tileSize, (row + 1) * tileSize);
				prev = grid[row][col];
			}
		}

		// draw horizontal lines
		for (int col = 0; col < grid.length; col++) {
			int prev = grid[0][col];
			for (int row = 1; row < grid.length; row++) {
				if (prev != grid[row][col])
					g.drawLine(col * tileSize, row * tileSize, (col + 1) * tileSize, row * tileSize);
				prev = grid[row][col];
			}
		}

		// fill the -1 square
		for (int row = 0; row < grid.length; row++)
			for (int col = 0; col < grid.length; col++)
				if (grid[row][col] == -1)
					g.fillRect(col * tileSize, row * tileSize, tileSize, tileSize);
	}

}
