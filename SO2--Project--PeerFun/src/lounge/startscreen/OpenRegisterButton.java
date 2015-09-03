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
import javax.swing.JButton;
import javax.swing.JPasswordField;
import javax.swing.JTextField;

public class OpenRegisterButton extends JButton implements ActionListener {

	JTextField loginField;
	JPasswordField passField;
	StartScreenModel startScreenModel;

	public OpenRegisterButton(String title, JTextField usernameField, JPasswordField passwordField, StartScreenModel startScreenModel) {
		super.setText(title);

		this.loginField = usernameField;
		this.passField = passwordField;
		this.startScreenModel = startScreenModel;

		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		startScreenModel.openRegisterPanel(loginField.getText(), passField.getPassword());
	}
	
}
