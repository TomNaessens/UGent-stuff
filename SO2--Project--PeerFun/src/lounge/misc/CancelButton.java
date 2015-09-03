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

class CancelButton extends JButton implements ActionListener {

	UserModel userModel;
	
	public CancelButton(String title, UserModel userModel) {
		super(title);
		
		this.userModel = userModel;
		
		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		userModel.closeFrame();
	}
	
}
