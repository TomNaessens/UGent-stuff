/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Controllers.Menu;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.JFrame;
import javax.swing.KeyStroke;

public class MenuBoodschappenAction extends AbstractAction {

	JFrame logger;

	public MenuBoodschappenAction(JFrame logger, String title) {
		super(title);

		putValue(Action.ACCELERATOR_KEY, KeyStroke.getKeyStroke("control B"));
		putValue(Action.MNEMONIC_KEY, new Integer(KeyEvent.VK_B));

		this.logger = logger;
	}

	public void actionPerformed(ActionEvent e) {
		logger.setVisible(!logger.isVisible());
	}

}
