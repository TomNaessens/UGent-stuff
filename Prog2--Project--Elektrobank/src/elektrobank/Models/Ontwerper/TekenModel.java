/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Models.Ontwerper;

import elektrobank.Models.EdgeCircuitModel;
import elektrobank.Models.ModelBeheerder;
import elektrobank.utils.ComponentMaker;
import elektrobank.utils.PointNode;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Point;
import java.awt.geom.Line2D;
import joldespice.components.Component;
import joldespice.graph.EdgeContainer;
import joldespice.graph.EdgeList;

public class TekenModel extends EdgeCircuitModel {

	// Models
	private SelectedActionModel saModel;
	private SelectedComponentModel scModel;
	private ModelBeheerder mBeheerder;
	// Declaratie van final static variabelen
	private static final int SNAP_DISTANCE = 20; // Als de afstand tussen 2 nodes kleiner is dan deze snapt hij er naartoe
	private static final int MIN_DISTANCE = 20; // Minimale afstand tussen 2 nodes om getekend te kunnen worden
	private static final int MIN_DEL_DISTANCE = 50; // Minimale afstand tussen muis & component
	private static final Color DRAW_COLOR = Color.BLUE;
	private static final Color SELECT_COLOR = Color.CYAN;
	private static final Color DELETE_COLOR = Color.RED;
	// Declaratie van algemene variabelen
	private Point beginPoint;
	private Point endPoint;

	public TekenModel(ModelBeheerder mBeheerder) {
		commitedEdge = null;
		
		saModel = new SelectedActionModel(mBeheerder);
		mBeheerder.setSAModel(saModel);

		scModel = mBeheerder.getSCModel();

		this.mBeheerder = mBeheerder;

		beginPoint = new Point(0, 0);
		endPoint = new Point(0, 0);

		setDimension(new Dimension(500, 200));
	}

	//
	// Methodes m.b.t. het tekenen van een nieuwe Edge
	//
	public void newEdge(Point pt) {
		beginPoint.setLocation(pt);
		endPoint.setLocation(pt);
		fireStateChanged();
	}

	public void changeEdge(Point pt) {
		if (pt.getX() < 0) {
			pt.setLocation(0, pt.getY());
		}
		if (pt.getY() < 0) {
			pt.setLocation(pt.getX(), 0);
		}
		endPoint.setLocation(pt);

		fireStateChanged();
	}

	public void commitEdge() {
		if (beginPoint.distance(endPoint) >= MIN_DISTANCE) {
			PointNode headNode;
			PointNode tailNode;

			PointNode tempNode = getNearestNode(beginPoint);

			// Snap naar ander beginpunt?
			if (tempNode != null) {
				if (tempNode.getLocation().distance(beginPoint) > SNAP_DISTANCE) {
					headNode = new PointNode(beginPoint);
					circ.addNode(headNode);
				} else {
					headNode = tempNode;
				}
			} else {
				headNode = new PointNode(beginPoint);
				circ.addNode(headNode);
			}

			tempNode = getNearestNode(endPoint);
			// Snap naar ander eindpunt?
			if (tempNode != null) {
				if (tempNode.getLocation().distance(endPoint) > SNAP_DISTANCE) {
					tailNode = new PointNode(endPoint);
					circ.addNode(tailNode);
				} else {
					tailNode = tempNode;
				}
			} else {
				tailNode = new PointNode(endPoint);
				circ.addNode(tailNode);
			}

			// Controleert als er geen nieuwe edges getrokken worden tussen 2 nodes die al verbonden zijn
			// controleert ook als de head en tailnode wel verschillend zijn
			if (!circ.areConnected(circ.nodeNumber(tailNode), circ.nodeNumber(headNode)) && tailNode != headNode) {
				// Clonen zodat we wel degelijk een nieuw object krijgen
				ComponentMaker compMaker = new ComponentMaker(mBeheerder.getPModel());
				Component component = compMaker.getCreateComponentMap().get(scModel.getSelected().getComponent());
				circ.addEdge(tailNode, headNode, component);
			}

		}

		beginPoint.setLocation(0, 0);
		endPoint.setLocation(0, 0);


		commitedEdge = null;
		mBeheerder.getPModel().setSelectedComponent(scModel.getSelected().getComponent());
		mBeheerder.getPModel().fire();

		updateDimension();

		fireStateChanged();
	}
	//
	// Methodes m.b.t. het verplaatsen van een node
	//
	PointNode selectedNode;
	EdgeContainer<Component, PointNode> selectedEdge;
	EdgeContainer<Component, PointNode> commitedEdge;

	public void selectNode(Point pt) {
		selectedNode = getNearestNode(pt);
		if (selectedNode != null) {
			if (selectedNode.getLocation().distance(pt) <= SNAP_DISTANCE) {
				selectedNode.setLocation(pt);
				selectedEdge = null;
				commitedEdge = null;
			} else {
				selectedNode = null;
			}
		}
		fireStateChanged();
	}

	public void moveNode(Point pt) {
		if (selectedNode != null) {
			selectedNode.setLocation(pt);
			fireStateChanged();
		}
	}

	public void placeNode(Point pt) {
		if (selectedNode != null) {
			PointNode dichtsteNode = getNearestNode(pt);

			if (dichtsteNode != null) {
				// Snap als de de node zich dichter in de buurt bevindt van een niet-buur node
				if (dichtsteNode.getLocation().distance(pt) <= SNAP_DISTANCE && !circ.areConnected(circ.nodeNumber(dichtsteNode), circ.nodeNumber(selectedNode))) {
					circ.mergeNode(dichtsteNode, selectedNode, dichtsteNode);
				}
			}
			selectedNode = null;

			updateDimension();
			fireStateChanged();
		}
	}

	public void getProperties(Point pt) {
		if (selectedEdge != null) {
			if (selectedEdge == commitedEdge) {
				commitedEdge = null;
			} else {
				commitedEdge = selectedEdge;
				mBeheerder.getPModel().setSelectedComponent(commitedEdge.getE().getClass().getSimpleName());
				//System.out.println(commitedEdge.getE().getClass());
			}
		} else {
			commitedEdge = null;
		}
		fireStateChanged();
	}

	//
	// Methodes m.b.t. het verwijderen van een edge
	//
	public void selectEdge(Point pt) {
		selectedEdge = getNearestEdge(pt);
		if (selectedEdge != null) {
			if (new Line2D.Double(selectedEdge.getHead().getLocation(), selectedEdge.getTail().getLocation()).ptSegDist(pt)
				   > MIN_DEL_DISTANCE) {
				selectedEdge = null;
			}
		}
		fireStateChanged();
	}

	public void deleteEdge(Point pt) {
		if (selectedEdge != null) {
			circ.purgeEdge(selectedEdge.getE());
			selectedEdge = getNearestEdge(pt); // Selecteert meteen een nieuwe Edge op basis van de huidige positie indien we muis niet verplaatst hebben
		}

		updateDimension();
		fireStateChanged();
	}

	//
	// Algemene utility methodes
	//
	// Geeft de dichtstbijzijnde node terug, als er geen is gevonden geeft hij null terug
	public PointNode getNearestNode(Point pt) {
		PointNode nearestNode = null;
		double shortest = Double.MAX_VALUE;
		double distanceToNode;
		PointNode[] nodeList = getCirc().getNodes();
		for (int i = 0; i < nodeList.length; i++) {
			distanceToNode = nodeList[i].getLocation().distance(pt);
			/*
			 * Laatste statement in deze if controleert als de node waarvan de afstand tot een punt gemeten wordt
			 * de afstand is naar een ander punt dan de geselecteerde node (niet naar zichzelf dus)
			 * Als selectedNode niet in gebruik is staat deze op null en zal dit dus geen problemen opleveren
			 */
			if (distanceToNode < shortest && circ.nodeNumber(selectedNode) != i) {
				nearestNode = circ.getNode(i);
				shortest = distanceToNode;
			}
		}
		return nearestNode;
	}

	// Geeft de dichtstbijzijnde Edge terug, als er geen is gevonden geeft hij null terug
	public EdgeContainer<Component, PointNode> getNearestEdge(Point pt) {
		EdgeContainer<Component, PointNode> nearestEdge = null;
		double shortest = Double.MAX_VALUE;
		double distanceToEdge;
		EdgeList<Component, PointNode> edges = circ.getEdgeList();

		for (EdgeContainer<Component, PointNode> tempEdge : edges) {
			PointNode headNode = tempEdge.getHead();
			PointNode tailNode = tempEdge.getTail();

			distanceToEdge = new Line2D.Double(headNode.getLocation(), tailNode.getLocation()).ptSegDist(pt);

			if (distanceToEdge < shortest) {
				shortest = distanceToEdge;
				nearestEdge = tempEdge;
			}
		}

		return nearestEdge;
	}

	// Zorgt ervan dat we dit van buitenaf kunnen laten hertekenen
	public void fire() {
		fireStateChanged();
	}

	//
	// Getters
	//
	public Point getBeginPunt() {
		return beginPoint;
	}

	public Point getEindPunt() {
		return endPoint;
	}

	public EdgeContainer<Component, PointNode> getSelectedEdge() {
		return selectedEdge;
	}

	public EdgeContainer<Component, PointNode> getCommitedEdge() {
		return commitedEdge;
	}

	public static Color getDELETE_COLOR() {
		return DELETE_COLOR;
	}

	public static Color getDRAW_COLOR() {
		return DRAW_COLOR;
	}

	public static Color getSELECT_COLOR() {
		return SELECT_COLOR;
	}
}
