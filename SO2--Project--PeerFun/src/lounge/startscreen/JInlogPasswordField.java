/**
 *
 * @author Tom Naessens 
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */

package lounge.startscreen;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JPasswordField;
import javax.swing.JTextField;

class JInlogPasswordField extends JPasswordField implements ActionListener {

	JTextField loginField;
	StartScreenModel startScreenModel;
	
	public JInlogPasswordField(int i, JTextField loginField, StartScreenModel startScreenModel) {
		super(i);
		
		this.loginField = loginField;
		this.startScreenModel = startScreenModel;
		
		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		startScreenModel.login(loginField.getText(), getPassword());
	}

}
