/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Models.Ontwerper;

import elektrobank.icons.SquareWaveIcon;
import elektrobank.icons.CapacitorIcon;
import elektrobank.icons.PWDiodeIcon;
import elektrobank.icons.DummyIcon;
import elektrobank.icons.DCPowerIcon;
import elektrobank.icons.IconPainter;
import elektrobank.icons.SwitchIcon;
import elektrobank.icons.InductorIcon;
import elektrobank.icons.CurrentSourceIcon;
import elektrobank.icons.ResistorIcon;
import elektrobank.icons.WireIcon;
import elektrobank.icons.ACPowerIcon;
import elektrobank.utils.Model;
import javax.swing.Icon;

/**
 *
 * @author tnaessens
 */
public class SelectedComponentModel extends Model {

	// Models
	SelectedActionModel saModel;
	// Icons
	private final IconPainter dummy;
	private IconPainter selected;
	private static final int ICONLENGTH = 60;
	private static final String[] ICONNAMES = {
		"Draad",
		"Gelijkspanning",
		"Wisselspanning",
		"Weerstand",
		"Spoel",
		"Condensator",
		"Blokgolf",
		"Diode",
		"Stroombron",
		"Schakelaar"
	};
	private static final IconPainter[] ICONLIST = {
		new WireIcon(),
		new DCPowerIcon(),
		new ACPowerIcon(),
		new ResistorIcon(),
		new InductorIcon(),
		new CapacitorIcon(),
		new SquareWaveIcon(),
		new PWDiodeIcon(),
		new CurrentSourceIcon(),
		new SwitchIcon(false)
	};

	public SelectedComponentModel(SelectedActionModel saModel) {
		this.saModel = saModel;

		this.dummy = new DummyIcon();
		selected = dummy;
	}

	public IconPainter getSelected() {
		return selected;
	}

	public void setSelected(IconPainter selected) {

		if (this.selected != dummy && saModel.getSelected() != saModel.getListener(2)) {
			saModel.setSelected(saModel.getListener(2));
		}

		if (this.selected != selected) {
			this.selected = selected;
			fireStateChanged();
		}

	}

	public void clearSelection() {

		if (this.selected != dummy) {
			this.selected = dummy;
			fireStateChanged();
		}
	}

	// Getters
	public static String[] getIconNames() {
		return ICONNAMES;
	}

	public static IconPainter[] getICONLIST() {
		return ICONLIST;
	}

	public static IconPainter getICON(int index) {
		return ICONLIST[index];
	}

	public static int getICONLENGTH() {
		return ICONLENGTH;
	}

	public Icon getDummy() {
		return dummy;
	}
}
