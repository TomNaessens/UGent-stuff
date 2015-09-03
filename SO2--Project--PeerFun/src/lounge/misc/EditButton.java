/**
 *
 * @author Tom Naessens
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package lounge.misc;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JButton;
import javax.swing.JPasswordField;
import javax.swing.JTextField;

class EditButton extends JButton implements ActionListener {

	UserModel userModel;

	JTextField usernameField;
	JPasswordField passwordField;
	JPasswordField newPasswordField;
	JPasswordField retypePasswordField;
	JTextField aliasField;
	
	EditButton(String title, JTextField usernameField, JPasswordField passwordField, JPasswordField newPasswordField, JPasswordField retypePasswordField, JTextField aliasField, UserModel userModel) {
		super(title);

		this.usernameField = usernameField;
		this.passwordField = passwordField;
		this.newPasswordField = newPasswordField;
		this.retypePasswordField = retypePasswordField;
		this.aliasField = aliasField;
		
		this.userModel = userModel;
		
		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		userModel.editUser(usernameField.getText(), passwordField.getPassword(), newPasswordField.getPassword(), retypePasswordField.getPassword(), aliasField.getText());
	}
}
