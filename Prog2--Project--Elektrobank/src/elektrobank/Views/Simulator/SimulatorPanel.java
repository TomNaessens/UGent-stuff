/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Views.Simulator;

import elektrobank.Models.Simulator.SimulatorModel;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import javax.swing.JPanel;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class SimulatorPanel extends JPanel implements ChangeListener, MouseListener {

	SimulatorModel sModel;

	public SimulatorPanel(SimulatorModel sModel) {

		setBackground(Color.white);
		setPreferredSize(new Dimension(500, 200));

		addMouseListener(this);

		this.sModel = sModel;

		sModel.addChangeListener(this);

	}

	@Override
	protected void paintComponent(Graphics g) {
		super.paintComponent(g);
		sModel.getSimulateHandler().paint(g);
	}

	public void stateChanged(ChangeEvent e) {
		revalidate();
		repaint();
	}

	@Override
	public Dimension getPreferredSize() {
		return sModel.getDimension();
	}

	public void mouseClicked(MouseEvent me) {
		sModel.getSimulateHandler().mouseClicked(me);
	}

	public void mousePressed(MouseEvent me) {
		sModel.getSimulateHandler().mousePressed(me);
	}

	public void mouseReleased(MouseEvent me) {
		sModel.getSimulateHandler().mouseReleased(me);
	}

	public void mouseEntered(MouseEvent me) {
		sModel.getSimulateHandler().mouseEntered(me);
	}

	public void mouseExited(MouseEvent me) {
		sModel.getSimulateHandler().mouseExited(me);
	}
}
