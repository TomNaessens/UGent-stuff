/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Models.Simulator;

import elektrobank.Controllers.Handlers.MouseHandler;
import elektrobank.Controllers.Handlers.SimulateMouseHandler;
import elektrobank.Controllers.TimerController;
import elektrobank.Models.EdgeCircuitModel;
import elektrobank.utils.PointNode;
import java.awt.Point;
import java.awt.geom.Line2D;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.swing.JOptionPane;
import javax.swing.SpinnerNumberModel;
import javax.swing.Timer;
import joldespice.circuit.simulator.CircuitSimulator;
import joldespice.circuit.simulator.NumericalException;
import joldespice.circuit.simulator.SimulatorFactory;
import joldespice.components.Component;
import joldespice.components.nonlinear.Switch;
import joldespice.graph.EdgeContainer;
import joldespice.graph.EdgeList;

public class SimulatorModel extends EdgeCircuitModel {

	MouseHandler simulateHandler;
	SpinnerNumberModel sSHModel;
	SpinnerNumberModel sSTModel;
	CircuitSimulator circSim;
	Timer timer;
	static final double MAXTHICKNESS = 5; // Want we willen niet dat onze lijnen TE dik getekend worden!
	double maxCurrent; // Zorgt ervoor dat we de damping zien op bepaalde momenten door de maximale stroom bij te houden
	double maxVoltage; // Zorgt ervoor dat we de damping zien op bepaalde momenten door de maximale voltage bij te houden

	public SimulatorModel(SpinnerNumberModel sSHModel, SpinnerNumberModel sSTModel) {
		simulateHandler = new SimulateMouseHandler(this);

		this.sSHModel = sSHModel;
		this.sSTModel = sSTModel;

		timer = new Timer((Integer) sSHModel.getValue(), new TimerController(this));

		circSim = SimulatorFactory.makeSimulator(circ);
	}

	public void initSim() {
		maxCurrent = 0;
		maxVoltage = 0;
		circSim = SimulatorFactory.makeSimulator(circ);
		circSim.init();
	}

	public void resetSim() {
		maxCurrent = 0;
		maxVoltage = 0;
		circSim.reset();
		timer.stop();
		fireStateChanged();
	}

	public void doStep() {
		try {
			circSim.setTimestep((Double) sSTModel.getValue());
			circSim.proceed();
			fireStateChanged();
		} catch (NumericalException ex) {
			Logger.getLogger("jOldeSpice").log(Level.SEVERE, "Matrix is singular", ex);
			JOptionPane.showMessageDialog(null, ex.getMessage(), "Fout opgetreden", JOptionPane.ERROR_MESSAGE);
			timer.stop();
		}
	}

	public void changeSwitch(Point pt) {
		EdgeContainer tempSwitch = getNearestSwitch(pt);
		if (tempSwitch != null) {
			((Switch) tempSwitch.getE()).setState(!((Switch) tempSwitch.getE()).getState());
		}
		fireStateChanged();
	}

	public void changeTimer() {
		if (timer.isRunning()) {
			timer.stop();
		} else {
			timer.start();
		}
		fireStateChanged();
	}

	// Geeft de dichtstbijzijnde Edge terug, als er geen is gevonden geeft hij null terug
	public EdgeContainer<Component, PointNode> getNearestSwitch(Point pt) {
		EdgeContainer<Component, PointNode> nearestEdge = null;
		double shortest = Double.MAX_VALUE;
		double distanceToEdge;
		EdgeList<Component, PointNode> edges = getCirc().getEdgeList();

		for (EdgeContainer<Component, PointNode> tempEdge : edges) {
			PointNode headNode = tempEdge.getHead();
			PointNode tailNode = tempEdge.getTail();

			distanceToEdge = new Line2D.Double(headNode.getLocation(), tailNode.getLocation()).ptSegDist(pt);

			if (tempEdge.getE().getClass().getSimpleName().equals("Switch") && distanceToEdge < shortest && distanceToEdge < 50) {
				shortest = distanceToEdge;
				nearestEdge = tempEdge;
			}
		}

		return nearestEdge;
	}

	public void setMaxCurrent(double current) {
		maxCurrent = current;
	}

	public double getMaxCurrent() {
		return maxCurrent;
	}

	public void setMaxVoltage(double voltage) {
		maxVoltage = voltage;
	}

	public double getMaxVoltage() {
		return maxVoltage;
	}

	public double getMaxThickness() {
		return MAXTHICKNESS;
	}

	public Timer getTimer() {
		return timer;
	}

	public MouseHandler getSimulateHandler() {
		return simulateHandler;
	}

}
