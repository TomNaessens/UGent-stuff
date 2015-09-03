/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Controllers.Menu;

import elektrobank.Models.ModelBeheerder;
import elektrobank.Models.Ontwerper.SelectedComponentModel;
import elektrobank.icons.IconPainter;
import java.awt.Color;
import java.awt.event.ActionEvent;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class MenuSelectedComponentController extends JCheckBoxMenuItem implements ItemListener, ChangeListener {

	private SelectedComponentModel scModel;
	private IconPainter icon;

	public MenuSelectedComponentController(ModelBeheerder mBeheerder, String title, IconPainter icon) {

		scModel = mBeheerder.getSCModel();

		this.icon = icon;
		//icon.setColor(Color.BLACK);
		icon.setColor(getBackground());
		super.setIcon(icon);
		super.setText(title);

		addItemListener(this);
		
		scModel.addChangeListener(this);
		setSelected(scModel.getSelected() == icon);
	}

	public void itemStateChanged(ItemEvent ie) {
		if (ie.getStateChange() == ItemEvent.SELECTED) {
			scModel.setSelected(icon);
		} else if(scModel.getSelected() == icon) {
			scModel.clearSelection();
		}
	}

	public void stateChanged(ChangeEvent ce) {
		setSelected(scModel.getSelected() == icon);
	}
}
