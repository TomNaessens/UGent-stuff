/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Controllers.Menu;

import elektrobank.Controllers.Handlers.MouseHandler;
import elektrobank.Models.Ontwerper.SelectedActionModel;
import java.awt.event.ActionEvent;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class MenuSelectedActionController extends JCheckBoxMenuItem implements ItemListener, ChangeListener {

	private SelectedActionModel saModel;
	private MouseHandler handler;

	public MenuSelectedActionController(SelectedActionModel saModel, String title, MouseHandler handler) {
		super(title);

		this.handler = handler;

		addItemListener(this);
		this.saModel = saModel;
		saModel.addChangeListener(this);
		setSelected(saModel.getSelected() == handler);
	}

	public void itemStateChanged(ItemEvent ie) {
		if (ie.getStateChange() == ItemEvent.SELECTED) {
			saModel.setSelected(handler);
		} else if (saModel.getSelected() == handler) {
			saModel.clearSelection();
		}
	}

	public void stateChanged(ChangeEvent ce) {
		setSelected(saModel.getSelected() == handler);
	}
}
