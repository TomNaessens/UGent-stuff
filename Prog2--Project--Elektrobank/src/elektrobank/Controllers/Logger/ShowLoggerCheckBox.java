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
import javax.swing.JCheckBox;

public class ShowLoggerCheckBox extends JCheckBox implements ActionListener {

	LoggerModel lModel;
	String title;

	public ShowLoggerCheckBox(LoggerModel lModel, String title) {
		super(title);
		this.lModel = lModel;
		this.title = title;

		addActionListener(this);
	}

	public void actionPerformed(ActionEvent e) {
		lModel.setShow(title, ((JCheckBox) e.getSource()).isSelected());
	}

}
