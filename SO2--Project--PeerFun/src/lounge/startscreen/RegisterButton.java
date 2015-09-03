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

public class RegisterButton extends OpenRegisterButton implements ActionListener {

	JTextField aliasField;
	JTextField birthdayField;
	
	public RegisterButton(String title, JTextField usernameField, JPasswordField passwordField, JTextField aliasField, StartScreenModel startScreenModel) {
		
		super(title, usernameField, passwordField, startScreenModel);

		this.aliasField = aliasField;
		this.birthdayField = birthdayField;


		// ActionListener moet hier niet worden toegevoegd, gebeurt al in de Superklasse!
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		startScreenModel.registerAccount(loginField.getText(), passField.getPassword(), aliasField.getText());
	}
}
