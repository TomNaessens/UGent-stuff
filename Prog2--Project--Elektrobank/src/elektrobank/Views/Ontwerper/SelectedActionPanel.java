/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Views.Ontwerper;

import elektrobank.Controllers.Buttons.SelectedActionController;
import elektrobank.Controllers.Handlers.MouseHandler;
import elektrobank.Models.ModelBeheerder;
import elektrobank.Models.Ontwerper.SelectedActionModel;
import java.awt.Dimension;
import java.awt.GridLayout;
import javax.swing.JPanel;

class SelectedActionPanel extends JPanel {

	private SelectedActionModel saModel;

	public SelectedActionPanel(ModelBeheerder mBeheerder) {
		saModel = mBeheerder.getSAModel();

		MouseHandler[] listeners = saModel.getListeners();
		String[] captions = saModel.getCAPTIONS();

		setLayout(new GridLayout(captions.length, 1));

		for(int i = 0; i < captions.length; i++) {
			add(new SelectedActionController(mBeheerder, captions[i], listeners[i]));
		}

	}
}
