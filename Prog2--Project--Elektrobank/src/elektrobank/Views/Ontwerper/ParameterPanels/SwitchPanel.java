/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Views.Ontwerper.ParameterPanels;

import elektrobank.Controllers.Buttons.ParameterButton;
import elektrobank.Models.Ontwerper.ParameterModel;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JButton;
import javax.swing.JPanel;

public class SwitchPanel extends JPanel {

	public SwitchPanel(ParameterModel pModel) {
		JButton button = new ParameterButton(pModel, "Open");
		add(button);
	}
}
