/**
 *
 * @author Tom Naessens
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package lounge.startscreen;

import java.awt.event.KeyEvent;
import javax.swing.GroupLayout;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JPasswordField;
import javax.swing.JTextField;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class StartScreen extends JPanel implements ChangeListener {

	StartScreenModel startScreenModel;
	
	JLabel loginLabel;
	JLabel passLabel;
	JTextField loginField;
	JPasswordField passField;
	LoginButton loginButton;
	OpenRegisterButton registerButton;
	
	public StartScreen(StartScreenModel startScreenModel) {
		this.startScreenModel = startScreenModel;
		
		loginLabel = new JLabel("Username:");
		passLabel = new JLabel("Password:");
		
		loginField = new JTextField(10);
		passField = new JInlogPasswordField(10, loginField, startScreenModel);
		
		registerButton = new OpenRegisterButton("Register", loginField, passField, startScreenModel);
		loginButton = new LoginButton("Login", loginField, passField, startScreenModel);
		
		GroupLayout layout = new GroupLayout(this);

		layout.setAutoCreateContainerGaps(true);
		
		layout.setVerticalGroup(
			   layout.createSequentialGroup()
			   	.addGroup(layout.createParallelGroup(GroupLayout.Alignment.BASELINE)
					.addComponent(loginLabel)
					.addComponent(loginField)
				)
				.addGroup(layout.createParallelGroup(GroupLayout.Alignment.BASELINE)
					.addComponent(passLabel)
					.addComponent(passField)
				)
				.addGroup(layout.createParallelGroup()
					.addComponent(registerButton)
					.addComponent(loginButton)
				)
		);

		layout.setHorizontalGroup(
			   layout.createSequentialGroup()
					.addGroup(layout.createParallelGroup()
						.addComponent(loginLabel)
						.addComponent(passLabel)
					)
					.addGroup(layout.createParallelGroup()
						.addComponent(loginField, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, 160)
						.addComponent(passField, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, 160)
						.addGroup(layout.createSequentialGroup()
							.addComponent(registerButton)
							.addComponent(loginButton)
						)
					)
		);

		setLayout(layout);
	}

	@Override
	public void stateChanged(ChangeEvent ce) {
		throw new UnsupportedOperationException("Not supported yet.");
	}
	
}
