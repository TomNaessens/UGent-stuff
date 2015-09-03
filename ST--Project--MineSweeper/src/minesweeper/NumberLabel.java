package minesweeper;


/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

import java.awt.Color;
import java.awt.event.MouseEvent;

public class NumberLabel extends MineLabel {

	private int number;
	private MineModel model;
	public NumberLabel(MineModel model, int x, int y, State state, int number) {
		super(model, x, y, state);
		
		this.model = model;
		this.number = number;
		
		this.setBackground(Color.green);		
	}
	
	@Override
	public void mouseClicked(MouseEvent me) {
		model.numberLabelClicked(this);
	}
	
	public int getNumber() {
		return number;
	}
	
}
