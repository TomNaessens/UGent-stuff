/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package minesweeper;

import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import javax.swing.JLabel;

public abstract class MineLabel extends JLabel implements MouseListener {

	private int x;
	private int y;
	private MineModel model;
	private State state;
	
	public MineLabel(MineModel model, int x, int y, State state) {
	
		setPreferredSize(model.getLabelDimension());
		
		
		this.model = model;
		this.x = x;
		this.y = y;
		
		this.setOpaque(true);
		
		addMouseListener(this);
	}

	
	public void setState(State state) {
		this.state = state;
	}

	@Override
	public void mouseClicked(MouseEvent me) {
		throw new UnsupportedOperationException("Not supported yet.");
	}

	@Override
	public void mousePressed(MouseEvent me) {
	}

	@Override
	public void mouseReleased(MouseEvent me) {
	}

	@Override
	public void mouseEntered(MouseEvent me) {
	}

	@Override
	public void mouseExited(MouseEvent me) {
	}
	
	
}
