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
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import javax.swing.JButton;
import javax.swing.JPasswordField;
import javax.swing.JTextField;

public class LoginButton extends JButton implements ActionListener {

	JTextField loginField;
	JPasswordField passField;
	StartScreenModel startScreenModel;
	
	LoginButton(String title, JTextField loginField, JPasswordField passField, StartScreenModel startScreenModel) {
		super.setText(title);
		
		this.loginField = loginField;
		this.passField = passField;
		this.startScreenModel = startScreenModel;
		
		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		startScreenModel.login(loginField.getText(), passField.getPassword());
	}
	
}
