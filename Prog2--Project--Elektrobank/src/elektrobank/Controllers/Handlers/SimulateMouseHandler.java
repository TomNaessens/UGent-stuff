/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Controllers.Handlers;

import elektrobank.Models.Simulator.SimulatorModel;
import elektrobank.icons.IconPainter;
import elektrobank.icons.SwitchIcon;
import elektrobank.utils.PointNode;
import java.awt.Color;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import java.awt.event.MouseEvent;
import javax.swing.event.MouseInputAdapter;
import joldespice.circuit.EdgeCircuit;
import joldespice.components.Component;
import joldespice.components.nonlinear.Switch;
import joldespice.graph.EdgeContainer;
import joldespice.graph.EdgeList;

public class SimulateMouseHandler extends MouseInputAdapter implements MouseHandler {

	private SimulatorModel sModel;

	public SimulateMouseHandler(SimulatorModel sModel) {
		this.sModel = sModel;
	}

	@Override
	public void mousePressed(MouseEvent e) {
		sModel.changeSwitch(e.getPoint());
	}

	public void paint(Graphics g) {
		Graphics2D g2 = (Graphics2D) g;
		int length;
		double angle;
		IconPainter icon;
		double current;
		double voltage;

		g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);

		EdgeCircuit circ = sModel.getCirc();
		EdgeList<Component, PointNode> edges = circ.getEdgeList();

		for (EdgeContainer<Component, PointNode> edge : edges) {

			PointNode headNode = edge.getHead();
			PointNode tailNode = edge.getTail();

			length = (int) headNode.getLocation().distance(tailNode.getLocation());
			angle = Math.atan2(tailNode.getY() - headNode.getY(), tailNode.getX() - headNode.getX());

			icon = sModel.getIconMap(edge.getE().getClass().getSimpleName());

			if (edge.getE().getClass().getSimpleName().equals("Switch")) {
				((SwitchIcon) icon).setOpen(((Switch) edge.getE()).getState());
			}

			// Kleur lijnen
			voltage = edge.getE().getVoltage();
			if (Math.abs(voltage) > sModel.getMaxVoltage()) {
				sModel.setMaxVoltage(Math.abs(voltage));
			}

			int kleur = (int) (Math.abs(voltage) / sModel.getMaxVoltage() * 255);

			if (voltage > 0) {
				icon.setColor(new Color(0, kleur, 0));
			} else if (voltage < 0) {
				icon.setColor(new Color(kleur, 0, 0));
			} else {
				icon.setColor(new Color(0, 0, 0));
			}

			// Dikte lijnen
			current = edge.getE().getCurrent();
			if (Math.abs(current) > sModel.getMaxCurrent()) {
				sModel.setMaxCurrent(current);
			}

			if (sModel.getMaxCurrent() == 0) {
				icon.setThickness(1);
			} else {
				icon.setThickness(Math.abs((float) (current / sModel.getMaxCurrent() * sModel.getMaxThickness())));
			}
			icon.setLength(length);
			icon.setAngle(angle);
			icon.paintIcon(null, g2, (headNode.getX() + tailNode.getX()) / 2 - icon.getIconWidth() / 2, (headNode.getY() + tailNode.getY()) / 2 - icon.getIconHeight() / 2);

			g2.fillOval(headNode.getX() - sModel.getNODE_SIZE() / 2, headNode.getY() - sModel.getNODE_SIZE() / 2, sModel.getNODE_SIZE(), sModel.getNODE_SIZE());
			g2.fillOval(tailNode.getX() - sModel.getNODE_SIZE() / 2, tailNode.getY() - sModel.getNODE_SIZE() / 2, sModel.getNODE_SIZE(), sModel.getNODE_SIZE());
		}
	}
}
