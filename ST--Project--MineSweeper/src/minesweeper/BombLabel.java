package minesweeper;

import java.awt.Color;
import java.awt.Dimension;

/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
public class BombLabel extends MineLabel {
	
	public BombLabel(MineModel model, int x, int y, State state) {
		super(model, x, y, state);
		
		this.setBackground(Color.red);
	}

}
