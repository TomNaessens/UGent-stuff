/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Controllers.Handlers;

import elektrobank.Models.Ontwerper.TekenModel;
import elektrobank.Models.ModelBeheerder;
import elektrobank.icons.IconPainter;
import elektrobank.icons.SwitchIcon;
import elektrobank.utils.PointNode;
import java.awt.Color;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import javax.swing.event.MouseInputAdapter;
import joldespice.circuit.EdgeCircuit;
import joldespice.components.Component;
import joldespice.components.nonlinear.Switch;
import joldespice.graph.EdgeContainer;
import joldespice.graph.EdgeList;

public class DummyMouseHandler extends MouseInputAdapter implements MouseHandler {

	private ModelBeheerder mBeheerder;
	private TekenModel tModel;

	public DummyMouseHandler(ModelBeheerder mBeheerder) {
		this.mBeheerder = mBeheerder;
	}

	public void paint(Graphics g) {
		tModel = mBeheerder.getTModel();

		Graphics2D g2 = (Graphics2D) g;
		int length;
		double angle;
		IconPainter icon;

		g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);

		EdgeCircuit circ = tModel.getCirc();

		EdgeList<Component, PointNode> edges = circ.getEdgeList();

		for (EdgeContainer<Component, PointNode> edge : edges) {
			PointNode headNode = edge.getHead();
			PointNode tailNode = edge.getTail();

			g2.fillOval(headNode.getX() - tModel.getNODE_SIZE() / 2, headNode.getY() - tModel.getNODE_SIZE() / 2, tModel.getNODE_SIZE(), tModel.getNODE_SIZE());

			length = (int) headNode.getLocation().distance(tailNode.getLocation());
			angle = Math.atan2(tailNode.getY() - headNode.getY(), tailNode.getX() - headNode.getX());
			icon = tModel.getIconMap(edge.getE().getClass().getSimpleName());
			
			if (edge.getE().getClass().getSimpleName().equals("Switch")) {
				((SwitchIcon) icon).setOpen(((Switch) edge.getE()).getState());
			}

			icon.setLength(length);
			icon.setColor(Color.black);
			icon.setAngle(angle);
			icon.setThickness(1);
			icon.paintIcon(null, g2, (headNode.getX() + tailNode.getX()) / 2 - icon.getIconWidth() / 2, (headNode.getY() + tailNode.getY()) / 2 - icon.getIconHeight() / 2);

			g2.fillOval(tailNode.getX() - tModel.getNODE_SIZE() / 2, tailNode.getY() - tModel.getNODE_SIZE() / 2, tModel.getNODE_SIZE(), tModel.getNODE_SIZE());
		}
	}
}
