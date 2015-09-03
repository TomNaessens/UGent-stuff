/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package minesweeper;

import java.awt.Dimension;
import java.awt.GridLayout;
import javax.swing.JPanel;
import javax.swing.event.ChangeListener;

public class GamePanel extends JPanel {

	MineModel model;
	
	public GamePanel(MineModel model) {
		
		GridLayout layout = new GridLayout(25, 25, 2, 2);
		
		setLayout(layout);
		
		setPreferredSize(new Dimension(600,400));
		
		this.model = model;
		model.initGrid();
		drawNewGame();
	}

	public void drawNewGame() {
		MineLabel[][] buttonGrid = model.getButtonGrid();
		for(int i = 0; i < buttonGrid.length; i++) {
			for(int j = 0; j < buttonGrid[i].length; j++) {
				add(buttonGrid[i][j]);
			}
		}
	}
	
}
