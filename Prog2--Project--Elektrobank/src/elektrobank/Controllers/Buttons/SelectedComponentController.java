/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Controllers.Buttons;

import elektrobank.Models.Ontwerper.ParameterModel;
import elektrobank.Models.Ontwerper.SelectedComponentModel;
import elektrobank.icons.IconPainter;
import java.awt.Color;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import javax.swing.JToggleButton;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class SelectedComponentController extends JToggleButton implements ItemListener, ChangeListener {

	private SelectedComponentModel scModel;
	private ParameterModel pModel;
	private IconPainter icon;
     
	public SelectedComponentController(SelectedComponentModel scModel, ParameterModel pModel, IconPainter icon) {

		this.icon = icon;
		icon.setColor(Color.BLACK);
		icon.setLength(scModel.getICONLENGTH());
		super.setIcon(icon);

		addItemListener(this);

		this.scModel = scModel;
		this.pModel = pModel;

		scModel.addChangeListener(this);
		setSelected(scModel.getSelected() == icon);
	}
	
	public void itemStateChanged(ItemEvent ie) {
		if (ie.getStateChange() == ItemEvent.SELECTED) {
			scModel.setSelected(icon);
			pModel.setSelectedComponent(icon.getComponent());
		} else if(scModel.getSelected() == icon) {
			pModel.clearPanel();
			scModel.clearSelection();
		}
	}

	public void stateChanged(ChangeEvent ce) {
		setSelected(scModel.getSelected() == icon);
	}
}
