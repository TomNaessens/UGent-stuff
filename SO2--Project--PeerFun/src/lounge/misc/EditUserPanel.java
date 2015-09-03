/**
 *
 * @author Tom Naessens
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package lounge.misc;

import java.awt.GridLayout;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JPasswordField;
import javax.swing.JTextField;
import userManagement.User;

public class EditUserPanel extends JPanel {

	JTextField usernameField;
	JPasswordField passwordField;
	JPasswordField newPasswordField;
	JPasswordField retypePasswordField;
	JTextField aliasField;
	JTextField birthdayField;

	public EditUserPanel(User user, UserModel userModel) {

		GridLayout layout = new GridLayout(6, 2);
		setLayout(layout);
		
		JLabel userNameLabel = new JLabel("* Username:");
		JLabel passwordLabel = new JLabel("* Old Password:");
		JLabel newPasswordLabel = new JLabel("New Password:");
		JLabel retypePasswordLabel = new JLabel("Retype Password:");
		JLabel realNameLabel = new JLabel("* Nickname:");


		usernameField = new JTextField(user.getName());
		usernameField.setEnabled(false);

		passwordField = new JPasswordField();
		newPasswordField = new JPasswordField();
		retypePasswordField = new JPasswordField();
		
		aliasField = new JTextField(user.getAlias());
		birthdayField = new JTextField();
		
		CancelButton cancelButton = new CancelButton("Cancel", userModel);
		EditButton editButton = new EditButton("Edit", usernameField, passwordField, newPasswordField, retypePasswordField, aliasField, userModel);

		add(userNameLabel);
		add(usernameField);
		
		add(passwordLabel);
		add(passwordField);
		
		add(newPasswordLabel);
		add(newPasswordField);
		
		add(retypePasswordLabel);
		add(retypePasswordField);
		
		add(realNameLabel);
		add(aliasField);
		
		add(cancelButton);
		add(editButton);
		
	}
}
