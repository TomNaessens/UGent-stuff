/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Controllers.Buttons;

import elektrobank.Controllers.Handlers.MouseHandler;
import elektrobank.Models.ModelBeheerder;
import elektrobank.Models.Ontwerper.SelectedActionModel;
import java.awt.event.ActionEvent;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import javax.swing.JToggleButton;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class SelectedActionController extends JToggleButton implements ItemListener, ChangeListener {

	private ModelBeheerder mBeheerder;
	private SelectedActionModel saModel;
	private MouseHandler handler;

	public SelectedActionController(ModelBeheerder mBeheerder, String title, MouseHandler handler) {
		super(title);

		this.mBeheerder = mBeheerder;

		this.handler = handler;

		addItemListener(this);

		this.saModel = mBeheerder.getSAModel();
		saModel.addChangeListener(this);
		setSelected(saModel.getSelected() == handler);
	}

	public void itemStateChanged(ItemEvent ie) {
		if (ie.getStateChange() == ItemEvent.SELECTED) {
			saModel.setSelected(handler);
		} else if (saModel.getSelected() == handler) {
			saModel.clearSelection();
		}
		mBeheerder.getPModel().clearPanel();
	}

	public void stateChanged(ChangeEvent ce) {
		setSelected(saModel.getSelected() == handler);
	}
}
