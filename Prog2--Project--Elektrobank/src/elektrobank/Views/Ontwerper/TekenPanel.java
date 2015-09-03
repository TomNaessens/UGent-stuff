/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Views.Ontwerper;

import elektrobank.Models.Ontwerper.TekenModel;
import elektrobank.Models.ModelBeheerder;
import elektrobank.Models.Ontwerper.SelectedActionModel;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.event.MouseEvent;
import javax.swing.JPanel;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.MouseInputListener;

public class TekenPanel extends JPanel implements ChangeListener, MouseInputListener {

	private TekenModel tModel;
	private SelectedActionModel saModel;

	public TekenPanel(ModelBeheerder mBeheerder) {

		setBackground(Color.white);

		this.tModel = mBeheerder.getTModel();
		tModel.addChangeListener(this);

		this.saModel = mBeheerder.getSAModel();
		saModel.addChangeListener(this);
	
		addMouseListener(this);
		addMouseMotionListener(this);
	}

	@Override
	public Dimension getPreferredSize() {
		return tModel.getDimension();
	}

	// DELEGATIE
	@Override
	public void paintComponent(Graphics g) {
		super.paintComponent(g);
		saModel.getSelected().paint(g);
	}

	public void stateChanged(ChangeEvent me) {
		revalidate();
		repaint();
	}

	public void mouseClicked(MouseEvent me) {
		saModel.getSelected().mouseClicked(me);
	}

	public void mousePressed(MouseEvent me) {
		saModel.getSelected().mousePressed(me);
	}

	public void mouseReleased(MouseEvent me) {
		saModel.getSelected().mouseReleased(me);
	}

	public void mouseEntered(MouseEvent me) {
		saModel.getSelected().mouseEntered(me);
	}

	public void mouseExited(MouseEvent me) {
		saModel.getSelected().mouseExited(me);
	}

	public void mouseDragged(MouseEvent me) {
		saModel.getSelected().mouseDragged(me);
	}

	public void mouseMoved(MouseEvent me) {
		saModel.getSelected().mouseMoved(me);
	}
}
