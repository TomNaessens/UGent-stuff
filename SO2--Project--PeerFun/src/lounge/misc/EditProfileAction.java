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
import javax.swing.AbstractAction;
import userManagement.User;

public class EditProfileAction extends AbstractAction {

	User user;
	UserModel userModel;
	
	public EditProfileAction(User user, UserModel userModel) {
		super("Edit profile");
		
		this.user = user;
		this.userModel = userModel;
	}
	
	@Override
	public void actionPerformed(ActionEvent ae) {
		userModel.openEditUserPanel();
	}
	
}
