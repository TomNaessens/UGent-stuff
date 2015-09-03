/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Models.Ontwerper;

import elektrobank.Controllers.Handlers.DummyMouseHandler;
import elektrobank.Controllers.Handlers.MouseHandler;
import elektrobank.Controllers.Handlers.MoveNodeMouseHandler;
import elektrobank.Controllers.Handlers.NewComponentMouseHandler;
import elektrobank.Controllers.Handlers.RemoveEdgeMouseHandler;
import elektrobank.Models.ModelBeheerder;
import elektrobank.utils.Model;

public class SelectedActionModel extends Model {

	// Models
	private ModelBeheerder mBeheerder;
	private SelectedComponentModel scModel;
	// Captions
	private static final String[] CAPTIONS = {
		"Verplaats een component",
		"Verwijder een component",
		"Voeg een component toe"
	};
	// Handlers
	private final MouseHandler dummy;
	private final MouseHandler[] listeners;

	public SelectedActionModel(ModelBeheerder mBeheerder) {
		this.mBeheerder = mBeheerder;
		
		scModel = new SelectedComponentModel(this);
		mBeheerder.setSCModel(scModel);

		listeners = new MouseHandler[]{
				   new MoveNodeMouseHandler(mBeheerder),
				   new RemoveEdgeMouseHandler(mBeheerder),
				   new NewComponentMouseHandler(mBeheerder)
			   };

		this.dummy = new DummyMouseHandler(mBeheerder);
		selected = dummy;
	}
	private MouseHandler selected;

	public MouseHandler getSelected() {
		return selected;
	}

	public void setSelected(MouseHandler selected) {

		if (selected == listeners[2] && scModel.getSelected() == scModel.getDummy()) {
			scModel.setSelected(scModel.getICON(0));
			fireStateChanged();
		} else {
			scModel.clearSelection();
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
	public String[] getCAPTIONS() {
		return CAPTIONS;
	}

	public MouseHandler[] getListeners() {
		return listeners;
	}

	public MouseHandler getListener(int index) {
		return listeners[index];
	}

	public MouseHandler getDummy() {
		return dummy;
	}
}
