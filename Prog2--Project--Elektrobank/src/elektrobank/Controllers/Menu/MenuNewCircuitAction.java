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
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.JOptionPane;
import javax.swing.KeyStroke;

public class MenuNewCircuitAction extends AbstractAction {

	private ModelBeheerder mBeheerder;

	public MenuNewCircuitAction(ModelBeheerder mBeheerder, String title) {
		super(title);
		putValue(Action.ACCELERATOR_KEY, KeyStroke.getKeyStroke("control N"));
		putValue(Action.MNEMONIC_KEY, new Integer(KeyEvent.VK_N));
	
		this.mBeheerder = mBeheerder;
	}

	public void actionPerformed(ActionEvent e) {
		if (JOptionPane.showConfirmDialog(null, "Bent u zeker dat u het circuit wilt verwijderen?", "Opgelet!", JOptionPane.OK_CANCEL_OPTION) == 0) {
			mBeheerder.getSelected().clearAll();
			mBeheerder.getSModel().initSim();
		}
	}
}
