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
import elektrobank.Models.Ontwerper.SelectedComponentModel;
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

public class NewComponentMouseHandler extends MouseInputAdapter implements MouseHandler {

	private ModelBeheerder mBeheerder;
	private TekenModel tModel;
	private SelectedComponentModel scModel;

	public NewComponentMouseHandler(ModelBeheerder mBeheerder) {
		this.mBeheerder = mBeheerder;
		this.scModel = mBeheerder.getSCModel();
	}

	@Override
	public void mousePressed(MouseEvent e) {
		tModel.newEdge(e.getPoint());
	}

	@Override
	public void mouseDragged(MouseEvent e) {
		tModel.changeEdge(e.getPoint());
	}

	@Override
	public void mouseReleased(MouseEvent e) {
		tModel.commitEdge();
	}

	public void paint(Graphics g) {

		this.tModel = mBeheerder.getTModel();

		Graphics2D g2 = (Graphics2D) g;
		int length;
		double angle;
		IconPainter icon;

		g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);

		g2.setColor(Color.black);

		// Haalt het circuit op en haalt alle Componenten en edges er uit
		EdgeCircuit circ = tModel.getCirc();
		EdgeList<Component, PointNode> edges = circ.getEdgeList();

		for (EdgeContainer<Component, PointNode> edge : edges) {
			PointNode headNode = edge.getHead();
			PointNode tailNode = edge.getTail();

			g2.fillOval(headNode.getX() - tModel.getNODE_SIZE() / 2, headNode.getY() - tModel.getNODE_SIZE() / 2, tModel.getNODE_SIZE(), tModel.getNODE_SIZE());

			length = (int) Math.round(Math.sqrt((headNode.getX() - tailNode.getX()) * (headNode.getX() - tailNode.getX()) + (headNode.getY() - tailNode.getY()) * (headNode.getY() - tailNode.getY())));
			angle = Math.atan2(tailNode.getY() - headNode.getY(), tailNode.getX() - headNode.getX());
			icon = tModel.getIconMap(edge.getE().getClass().getSimpleName());
			if (edge.getE().getClass().getSimpleName().equals("Switch")) {
				((SwitchIcon) icon).setOpen(((Switch) edge.getE()).getState());
			}
			icon.setThickness(1);
			icon.setColor(Color.black);
			icon.setLength(length);
			icon.setAngle(angle);
			icon.paintIcon(null, g, (headNode.getX() + tailNode.getX()) / 2 - icon.getIconWidth() / 2, (headNode.getY() + tailNode.getY()) / 2 - icon.getIconHeight() / 2);

			g2.fillOval(tailNode.getX() - tModel.getNODE_SIZE() / 2, tailNode.getY() - tModel.getNODE_SIZE() / 2, tModel.getNODE_SIZE(), tModel.getNODE_SIZE());
		}

		// Tekent de lijn waar we op dit moment mee bezig zijn
		g2.setColor(tModel.getDRAW_COLOR());

		if (!(tModel.getBeginPunt().x == 0 && tModel.getEindPunt().x == 0 && tModel.getBeginPunt().y == 0 && tModel.getEindPunt().y == 0)
			   && mBeheerder.getSCModel().getSelected().getComponent() != null) {
			g2.fillOval(tModel.getBeginPunt().x - tModel.getNODE_SIZE() / 2, tModel.getBeginPunt().y - tModel.getNODE_SIZE() / 2, tModel.getNODE_SIZE(), tModel.getNODE_SIZE());

			length = (int) tModel.getBeginPunt().distance(tModel.getEindPunt());
			angle = Math.atan2(tModel.getEindPunt().y - tModel.getBeginPunt().y, tModel.getEindPunt().x - tModel.getBeginPunt().x);

			icon = tModel.getIconMap(scModel.getSelected().getComponent());

			if (mBeheerder.getSCModel().getSelected().getComponent().equals("Switch")) {
				((SwitchIcon) icon).setOpen(mBeheerder.getPModel().getClosed());
			}


			icon.setLength(length);
			icon.setColor(Color.blue);
			icon.setThickness(1);
			icon.setAngle(angle);
			icon.paintIcon(null, g2, (tModel.getBeginPunt().x + tModel.getEindPunt().x) / 2 - icon.getIconWidth() / 2, (tModel.getBeginPunt().y + tModel.getEindPunt().y) / 2 - icon.getIconHeight() / 2);


			g2.fillOval(tModel.getEindPunt().x - tModel.getNODE_SIZE() / 2, tModel.getEindPunt().y - tModel.getNODE_SIZE() / 2, tModel.getNODE_SIZE(), tModel.getNODE_SIZE());
		}


	}
}
