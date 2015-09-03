/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Controllers.Logger;

import elektrobank.Models.Logger.LoggerModel;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.logging.Level;
import javax.swing.JComboBox;

public class LoggerLevelChanged implements ActionListener {

	LoggerModel lModel;

	public LoggerLevelChanged(LoggerModel lModel) {
		this.lModel = lModel;
	}

	public void actionPerformed(ActionEvent e) {
		lModel.setLevel((Level) ((JComboBox) e.getSource()).getModel().getSelectedItem());
	}

}
