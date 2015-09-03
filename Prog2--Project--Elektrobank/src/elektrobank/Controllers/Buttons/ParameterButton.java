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
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JButton;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class ParameterButton extends JButton implements ActionListener, ChangeListener {

	private ParameterModel pModel;

	public ParameterButton(ParameterModel pModel, String title) {
		super(title);
		this.pModel = pModel;

		addActionListener(this);
		pModel.addChangeListener(this);
	}

	public void stateChanged(ChangeEvent e) {
		if(pModel.getClosed()) {
			setText("Zet open");
		} else {
			setText("Zet dicht");
		}
	}

	public void actionPerformed(ActionEvent e) {
		pModel.setClosed(!pModel.getClosed());
	}
}
