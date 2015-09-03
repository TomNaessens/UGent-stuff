/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Models;

import elektrobank.Models.Logger.LoggerModel;
import elektrobank.Models.Ontwerper.ParameterModel;
import elektrobank.Models.Ontwerper.TekenModel;
import elektrobank.Models.Ontwerper.SelectedComponentModel;
import elektrobank.Models.Simulator.SimulatorModel;
import elektrobank.Models.Ontwerper.SelectedActionModel;
import javax.swing.DefaultListModel;
import javax.swing.SpinnerNumberModel;

public class ModelBeheerder {

	TekenModel tModel;
	SelectedActionModel saModel;
	SelectedComponentModel scModel;
	SimulatorModel sModel;
	EdgeCircuitModel selected;
	SpinnerNumberModel sSHModel;
	SpinnerNumberModel sTSModel;
	LoggerModel lModel;
	ParameterModel pModel;
	DefaultListModel logListModel;
	TabbedModel tabModel;

	public ModelBeheerder() {
		tModel = new TekenModel(this); // Model dat het tekenen beheert

		sSHModel = new SpinnerNumberModel(100, 50, 1000, 50);
		sTSModel = new SpinnerNumberModel(0.001, 0.001, 100, 0.001);
		sModel = new SimulatorModel(sSHModel, sTSModel); // Spinnermodellen registreren bij SimulatorModel zodat we aan hun info kunnen opvragen

		tabModel = new TabbedModel(this);

		pModel = new ParameterModel(this);

		selected = tModel;
	}

	public TekenModel getTModel() {
		return tModel;
	}

	public SelectedActionModel getSAModel() {
		return saModel;
	}

	public SelectedComponentModel getSCModel() {
		return scModel;
	}

	public SimulatorModel getSModel() {
		return sModel;
	}

	public SpinnerNumberModel getSSHModel() {
		return sSHModel;
	}

	public SpinnerNumberModel getSTSModel() {
		return sTSModel;
	}

	public LoggerModel getLoggerModel() {
		return lModel;
	}

	public DefaultListModel getLogListModel() {
		return logListModel;
	}

	public ParameterModel getPModel() {
		return pModel;
	}

	public TabbedModel getTabModel() {
		return tabModel;
	}

	public void setlModel(LoggerModel lModel) {
		this.lModel = lModel;
	}

	public void setLogListModel(DefaultListModel logListModel) {
		this.logListModel = logListModel;
	}

	public void setSAModel(SelectedActionModel saModel) {
		this.saModel = saModel;
	}

	public void setSCModel(SelectedComponentModel scModel) {
		this.scModel = scModel;
	}

	public void setTModel(TekenModel tModel) {
		this.tModel = tModel;
	}

	public void setSelected(EdgeCircuitModel model) {
		selected = model;
	}

	public EdgeCircuitModel getSelected() {
		return selected;
	}

	public void setPModel(ParameterModel pModel) {
		this.pModel = pModel;
	}
}
