/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Models.Ontwerper;

import elektrobank.Models.ModelBeheerder;
import elektrobank.Views.Ontwerper.ParameterPanels.ACPowerPanel;
import elektrobank.Views.Ontwerper.ParameterPanels.CapacitatorPanel;
import elektrobank.Views.Ontwerper.ParameterPanels.CurrentSourcePanel;
import elektrobank.Views.Ontwerper.ParameterPanels.DCPowerPanel;
import elektrobank.Views.Ontwerper.ParameterPanels.InductorPanel;
import elektrobank.Views.Ontwerper.ParameterPanels.PWDiodePanel;
import elektrobank.Views.Ontwerper.ParameterPanels.ResistorPanel;
import elektrobank.Views.Ontwerper.ParameterPanels.SquareWavePanel;
import elektrobank.Views.Ontwerper.ParameterPanels.SwitchPanel;
import elektrobank.Views.Ontwerper.ParameterPanels.WirePanel;
import elektrobank.utils.ComponentMaker;
import elektrobank.utils.Model;
import java.util.HashMap;
import javax.swing.JPanel;
import joldespice.components.Component;
import joldespice.components.differential.Capacitor;
import joldespice.components.differential.Inductor;
import joldespice.components.linear.ACPower;
import joldespice.components.linear.CurrentSource;
import joldespice.components.linear.DCPower;
import joldespice.components.linear.Resistor;
import joldespice.components.linear.SquareWave;
import joldespice.components.linear.Wire;
import joldespice.components.nonlinear.PWDiode;
import joldespice.components.nonlinear.Switch;

public class ParameterModel extends Model {

	private static final int TEXTFIELD_LENGTH = 8;
	private HashMap<String, JPanel> panelMap;
	private JPanel selectedPanel;
	private double[] waardes;
	private boolean closed;
	private ModelBeheerder mBeheerder;

	public ParameterModel(ModelBeheerder mBeheerder) {
		this.mBeheerder = mBeheerder;
		waardes = new double[]{0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0};
		closed = true;

		mBeheerder.setPModel(this); // Hack zodat de dingen die we vanaf nu initialiseren geen nullpointers
		// krijgen als we later dit model aan de beheerder opvragen

		panelMap = new HashMap<String, JPanel>();
		panelMap.put("Wire", new WirePanel()); // Is hier eigenlijk meer een dummy!
		panelMap.put("DCPower", new DCPowerPanel(mBeheerder));
		panelMap.put("ACPower", new ACPowerPanel(mBeheerder));
		panelMap.put("Resistor", new ResistorPanel(mBeheerder));
		panelMap.put("Inductor", new InductorPanel(mBeheerder));
		panelMap.put("Capacitor", new CapacitatorPanel(mBeheerder));
		panelMap.put("SquareWave", new SquareWavePanel(mBeheerder));
		panelMap.put("PWDiode", new PWDiodePanel(mBeheerder));
		panelMap.put("CurrentSource", new CurrentSourcePanel(mBeheerder));
		panelMap.put("Switch", new SwitchPanel(this));
	}

	public void clearPanel() {
		setSelectedComponent("Wire");
		fireStateChanged();
	}

	//
	// SETTERS
	//
	public void setSelectedComponent(String component) {
		selectedPanel = panelMap.get(component);
		ComponentMaker compMaker = new ComponentMaker(this);
		Component comp;
		if (mBeheerder.getTModel().getCommitedEdge() != null) { // Component is geselecteerd: haal waarden op
			comp = mBeheerder.getTModel().getCommitedEdge().getE();
		} else { // Zet nieuwe waarden aan de hand van het geselecteerde component
			comp = compMaker.getDefaultComponentMap().get(component);
		}

		if (comp instanceof Wire) {
		}
		if (comp instanceof ACPower) {
			waardes[1] = ((ACPower) comp).getAmplitude();
			waardes[2] = ((ACPower) comp).getOffset();
			waardes[3] = ((ACPower) comp).getFrequency();
			waardes[4] = ((ACPower) comp).getPhase();
		}
		if (comp instanceof Capacitor) {
			waardes[7] = ((Capacitor) comp).getCapacitance();
		}
		if (comp instanceof CurrentSource) {
			waardes[9] = ((CurrentSource) comp).getShortCircuitCurrent();
		}
		if (comp instanceof DCPower) {
			waardes[0] = ((DCPower) comp).getOpenCircuitVoltage();
		}
		if (comp instanceof Inductor) {
			waardes[6] = ((Inductor) comp).getInductance();
		}
		if (comp instanceof PWDiode) {
			waardes[8] = ((PWDiode) comp).getForwardVoltageDrop();
		}
		if (comp instanceof Resistor) {
			waardes[5] = ((Resistor) comp).getResistance();
		}
		if (comp instanceof SquareWave) {
			waardes[1] = ((SquareWave) comp).getAmplitude();
			waardes[2] = ((SquareWave) comp).getOffset();
			waardes[3] = ((SquareWave) comp).getFrequency();
			waardes[4] = ((SquareWave) comp).getPhase();
		}
		if (comp instanceof Switch) {
			setClosed(((Switch) comp).getState());
		}

		fireStateChanged();
	}

	public void setWaarde(double waarde, int i) {
		waardes[i] = waarde;
		ComponentMaker compMaker = new ComponentMaker(this);
		Component comp;

		if (mBeheerder.getTModel().getCommitedEdge() != null) {
			comp = mBeheerder.getTModel().getCommitedEdge().getE();
		} else {
			comp = compMaker.getDefaultComponentMap().get(mBeheerder.getSCModel().getSelected().getComponent());
		}
		if (comp instanceof Wire) {
		}
		if (comp instanceof ACPower) {
			((ACPower) comp).setParameters(waardes[1], waardes[2], waardes[3], waardes[4]);
		}
		if (comp instanceof Capacitor) {
			((Capacitor) comp).setCapacitance(waardes[7]);
		}
		if (comp instanceof CurrentSource) {
			((CurrentSource) comp).setShortCircuitCurrent(waardes[9]);
		}
		if (comp instanceof DCPower) {
			((DCPower) comp).setOpenCircuitVoltage(waardes[5]);
		}
		if (comp instanceof Inductor) {
			((Inductor) comp).setInductance(waardes[6]);
		}
		if (comp instanceof PWDiode) {
			((PWDiode) comp).setForwardVoltageDrop(waardes[8]);
		}
		if (comp instanceof Resistor) {
			((Resistor) comp).setResistance(waardes[5]);
		}
		if (comp instanceof SquareWave) {
			((SquareWave) comp).setParameters(waardes[1], waardes[2], waardes[3], waardes[4]);
		}
		if (comp instanceof Switch) {
			((Switch) comp).setState(closed);
		}
		fireStateChanged();
	}

	public void setClosed(boolean closed) {
		this.closed = closed;

		ComponentMaker compMaker = new ComponentMaker(this);
		Component comp;

		if (mBeheerder.getTModel().getCommitedEdge() != null) {
			comp = mBeheerder.getTModel().getCommitedEdge().getE();
		} else {
			comp = compMaker.getDefaultComponentMap().get(mBeheerder.getSCModel().getSelected().getComponent());
		}

		((Switch) comp).setState(closed);

		fireStateChanged();
		mBeheerder.getTModel().fire();
	}

	public void fire() {
		fireStateChanged();
	}

	//
	// GETTERS
	//
	public JPanel getSelectedComponent() {
		return selectedPanel;
	}

	public double getWaarde(int i) {
		return waardes[i];
	}

	public double[] getWaardes() {
		return waardes;
	}

	public boolean getClosed() {
		return closed;
	}

	public int getTextFieldLength() {
		return TEXTFIELD_LENGTH;
	}
}
