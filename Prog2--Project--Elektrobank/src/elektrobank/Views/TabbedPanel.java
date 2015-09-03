/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Views;

import elektrobank.Views.Simulator.SimulatorTabPanel;
import elektrobank.Views.Ontwerper.OntwerperTabPanel;
import elektrobank.Models.ModelBeheerder;
import elektrobank.Models.Ontwerper.SelectedActionModel;
import elektrobank.Models.TabbedModel;
import javax.swing.JPanel;
import javax.swing.JTabbedPane;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class TabbedPanel extends JTabbedPane implements ChangeListener {

	//Static SelectedAtionModel zodat deze te gebruiken is binnen de anonieme klasse
	private TabbedModel tabModel;

	public TabbedPanel(ModelBeheerder mBeheerder) {

		JPanel ontwerperTabbedPanel = new OntwerperTabPanel(mBeheerder);
		add("Ontwerp", ontwerperTabbedPanel);

		JPanel simulatorTabbedPanel = new SimulatorTabPanel(mBeheerder);
		add("Simuleer", simulatorTabbedPanel);

		setTabPlacement(JTabbedPane.BOTTOM);

		this.tabModel = mBeheerder.getTabModel();

		addChangeListener(this);

		tabModel.addChangeListener(this);
	}

	public void stateChanged(ChangeEvent e) {
		if (tabModel.getSelectedTab() != getSelectedIndex()) {
			tabModel.setSelectedTab(getSelectedIndex());
		}
	}
}
