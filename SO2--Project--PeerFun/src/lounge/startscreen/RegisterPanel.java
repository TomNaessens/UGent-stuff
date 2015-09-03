/**
 *
 * @author Tom Naessens
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package lounge.startscreen;

import java.awt.GridLayout;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JPasswordField;
import javax.swing.JTextField;

public class RegisterPanel extends JPanel {

	StartScreenModel startScreenModel;
	
	JTextField usernameField;
	JPasswordField passwordField;
	JTextField aliasField;
	
	public RegisterPanel(StartScreenModel startScreenModel, String userName, char[] password) {
		this.startScreenModel = startScreenModel;
		
		GridLayout layout = new GridLayout(4, 2);
		setLayout(layout);
		
		JLabel userNameLabel = new JLabel("* Username:");
		JLabel passwordLabel = new JLabel("* Password:");
		JLabel realNameLabel = new JLabel("* Nickname:");
		
		usernameField = new JTextField(userName);
		passwordField = new JPasswordField(new String(password));
		aliasField = new JTextField();
		
		RegisterButton registerButton = new RegisterButton("Register", usernameField, passwordField, aliasField, startScreenModel);
		
		add(userNameLabel);
		add(usernameField);
		add(passwordLabel);
		add(passwordField);
		add(realNameLabel);
		add(aliasField);
		add(new JLabel());
		add(registerButton);
	}
	
}
