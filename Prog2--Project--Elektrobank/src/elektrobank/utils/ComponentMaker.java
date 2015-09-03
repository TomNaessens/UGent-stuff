/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.utils;

import elektrobank.Models.Ontwerper.ParameterModel;
import java.util.HashMap;
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

public class ComponentMaker {

	private static final double GELIJKSPANNING_VOLT = 5;
	private static final double WISSELSPANNING_AMPLITUDE = 220;
	private static final double WISSELSPANNING_OFFSET = 0;
	private static final double WISSELSPANNING_FREQUENTIE = 50;
	private static final double WISSELSPANNING_FASE = 0;
	private static final double WEERSTAND_WEERSTAND = 100;
	private static final double SPOEL_ZELFINDUCTIE = 10e-3;
	private static final double CONDENSATOR_CAPACITEIT = 100e-9;
	private static final double BLOKGOLF_AMPLITUDE = 2.5;
	private static final double BLOKGOLF_OFFSET = 2.5;
	private static final double BLOKGOLF_FREQUENTIE = 5;
	private static final double BLOKGOLF_FASE = 0;
	private static final double DIODE_SPANNINGSVAL = 0.8;
	private static final double STROOMBRON_STROOM = 10e-3;
	private static final HashMap<String, Component> DEFAULTCOMPONENTMAP =
		   new HashMap<String, Component>() {

			   {
				   put("Wire", new Wire());
				   put("DCPower", new DCPower(GELIJKSPANNING_VOLT));
				   put("ACPower", new ACPower(WISSELSPANNING_AMPLITUDE, WISSELSPANNING_OFFSET, WISSELSPANNING_FREQUENTIE, WISSELSPANNING_FASE));
				   put("Resistor", new Resistor(WEERSTAND_WEERSTAND));
				   put("Inductor", new Inductor(SPOEL_ZELFINDUCTIE));
				   put("Capacitor", new Capacitor(CONDENSATOR_CAPACITEIT));
				   put("SquareWave", new SquareWave(BLOKGOLF_AMPLITUDE, BLOKGOLF_OFFSET, BLOKGOLF_FREQUENTIE, BLOKGOLF_FASE));
				   put("PWDiode", new PWDiode(DIODE_SPANNINGSVAL));
				   put("CurrentSource", new CurrentSource(STROOMBRON_STROOM));
				   put("Switch", new Switch(false));
			   }
		   };
	
	private HashMap<String, Component> createComponentMap;

	public ComponentMaker(ParameterModel pModel) {
		createComponentMap = new HashMap<String, Component>();
		createComponentMap.put("Wire", new Wire());
		createComponentMap.put("DCPower", new DCPower(pModel.getWaarde(0)));
		createComponentMap.put("ACPower", new ACPower(pModel.getWaarde(1), pModel.getWaarde(2), pModel.getWaarde(3), pModel.getWaarde(4)));
		createComponentMap.put("Resistor", new Resistor(pModel.getWaarde(5)));
		createComponentMap.put("Inductor", new Inductor(pModel.getWaarde(6)));
		createComponentMap.put("Capacitor", new Capacitor(pModel.getWaarde(7)));
		createComponentMap.put("SquareWave", new SquareWave(pModel.getWaarde(1), pModel.getWaarde(2), pModel.getWaarde(3), pModel.getWaarde(4)));
		createComponentMap.put("PWDiode", new PWDiode(pModel.getWaarde(8)));
		createComponentMap.put("CurrentSource", new CurrentSource(pModel.getWaarde(9)));
		createComponentMap.put("Switch", new Switch(pModel.getClosed()));
	}

	public static HashMap<String, Component> getDefaultComponentMap() {
		return DEFAULTCOMPONENTMAP;
	}

	public HashMap<String, Component> getCreateComponentMap() {
		return createComponentMap;
	}
}
