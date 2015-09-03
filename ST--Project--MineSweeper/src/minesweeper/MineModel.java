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
import minesweeper.MineLabel;
import minesweeper.utils.Model;

public class MineModel extends Model {
	
	private static final Dimension BUTTON_DIMENSION = new Dimension(10,10);
	
	private MineLabel[][] buttonGrid;
	private GamePanel gamePanel;

	public MineModel() {
	}
	
	public void initGrid() {
		buttonGrid = new MineLabel[25][25];
		
		for(int i = 0; i < 25; i++) {
			for(int j = 0; j < 25; j++) {
				buttonGrid[i][j] = new NumberLabel(this, i, j, State.BLANK, 0);
			}
		}
	}
	
	public Dimension getLabelDimension() {
		return BUTTON_DIMENSION;
	}
	
	public void numberLabelClicked(NumberLabel numberLabel) {
		numberLabel.setState(State.SHOWED);
	}

	public MineLabel[][] getButtonGrid() {
		return buttonGrid;
	}
	
	public void setGamePanel(GamePanel gamepanel) {
		this.gamePanel = gamepanel;
	}
}
