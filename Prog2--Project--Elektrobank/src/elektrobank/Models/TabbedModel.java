/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Models;

import elektrobank.utils.Model;

public class TabbedModel extends Model {

	private ModelBeheerder mBeheerder;
	private int selectedTab;

	public TabbedModel(ModelBeheerder mBeheerder) {
		this.mBeheerder = mBeheerder;
	}

	public void setSelectedTab(int i) {
		selectedTab = i;

		if (selectedTab == 0) {
			mBeheerder.getSAModel().setSelected(mBeheerder.getSAModel().getDummy());
			mBeheerder.setSelected(mBeheerder.getTModel());
			mBeheerder.getSModel().resetSim();
			mBeheerder.getSelected().updateDimension();
		} else {
			mBeheerder.getSModel().initSim();
			mBeheerder.setSelected(mBeheerder.getSModel());
			mBeheerder.getSelected().updateDimension();
		}
		
		fireStateChanged();
	}

	public int getSelectedTab() {
		return selectedTab;
	}
}
