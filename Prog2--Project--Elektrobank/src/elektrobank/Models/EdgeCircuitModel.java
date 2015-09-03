/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Models;

import elektrobank.icons.ACPowerIcon;
import elektrobank.icons.CapacitorIcon;
import elektrobank.icons.CurrentSourceIcon;
import elektrobank.icons.DCPowerIcon;
import elektrobank.icons.IconPainter;
import elektrobank.icons.InductorIcon;
import elektrobank.icons.PWDiodeIcon;
import elektrobank.icons.ResistorIcon;
import elektrobank.icons.SquareWaveIcon;
import elektrobank.icons.SwitchIcon;
import elektrobank.icons.WireIcon;
import elektrobank.utils.Model;
import elektrobank.utils.PointNode;
import java.awt.Dimension;
import java.util.HashMap;
import java.util.logging.Level;
import joldespice.circuit.EdgeCircuit;
import joldespice.components.Component;
import joldespice.graph.Graph;

public abstract class EdgeCircuitModel extends Model {

	// Ik kies hier voor protected zodat de subklasses hier gemakkelijk van gebruik kunnen maken zonder
	// iedere keer de getter op te roepen.
	// Static omdat ik van 2 instanties van deze klasse steeds hetzelfde circuit wil behouden.
	protected static EdgeCircuit<PointNode, Component> circ;

	private static Dimension dimensie;

	private static final int NODE_SIZE = 4; // Grootte van de ovaal dat een node voorstelt
	private static final HashMap<String, IconPainter> ICONMAP =
		   new HashMap<String, IconPainter>() {

			   {
				   put("Wire", new WireIcon());
				   put("DCPower", new DCPowerIcon());
				   put("ACPower", new ACPowerIcon());
				   put("Resistor", new ResistorIcon());
				   put("Inductor", new InductorIcon());
				   put("Capacitor", new CapacitorIcon());
				   put("SquareWave", new SquareWaveIcon());
				   put("PWDiode", new PWDiodeIcon());
				   put("CurrentSource", new CurrentSourceIcon());
				   put("Switch", new SwitchIcon(true));
			   }
		   };

	public EdgeCircuitModel() {
		circ = new EdgeCircuit(PointNode.class);
	}

	//
	// SETTERS
	//
	public EdgeCircuitModel(EdgeCircuit<PointNode, Component> circ) {
		this.circ = circ;
	}

	// Verwijdert alles
	public void clearAll() {
		joldespice.JOldeSpice.LOGGER.log(Level.INFO, "Nieuw circuit geladen");
		circ = new EdgeCircuit<PointNode, Component>(PointNode.class);
		setDimension(new Dimension());
		fireStateChanged();
	}

	// Nieuw circuit voor inladen
	public void setCirc(EdgeCircuit circ) {
		this.circ = circ;
		fireStateChanged();
	}

	public void updateDimension() {
		int maxWidth = 0;
		int maxHeigth = 0;

		PointNode[] nodeList = circ.getNodes();
		for(PointNode node : nodeList) {
			maxWidth = Math.max(maxWidth, node.getX());
			maxHeigth = Math.max(maxHeigth, node.getY());
		}
		setDimension(new Dimension(maxWidth + 50, maxHeigth + 50));
	}

	public void setDimension(Dimension dimensie) {
		this.dimensie = dimensie;
		fireStateChanged();
	}

	//
	// GETTERS
	//
	public static IconPainter getIconMap(String component) {
		return ICONMAP.get(component);
	}

	// Geeft het circuit terug
	public EdgeCircuit<PointNode, Component> getCirc() {
		return circ;
	}

	public static int getNODE_SIZE() {
		return NODE_SIZE;
	}

	// Geeft de dimensie terug
	public Dimension getDimension() {
		return dimensie;
	}
}
