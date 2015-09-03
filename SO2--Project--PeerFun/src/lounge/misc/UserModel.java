/**
 *
 * @author Tom Naessens
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package lounge.misc;

import chat.Chat;
import fileInteraction.UserFileWriter;
import java.util.ArrayList;
import java.util.Iterator;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import lounge.AbstractLoungeModel;
import network.NetworkAdapter;
import userManagement.CryptoManager;
import userManagement.Friend;
import userManagement.User;

public class UserModel {

	JFrame editUserFrame;
	User user;
	AbstractLoungeModel abstractLoungeModel;

	public UserModel(AbstractLoungeModel abstractLoungeModel, User currentUser) {
		this.abstractLoungeModel = abstractLoungeModel;
		this.user = currentUser;
	}

	public void openEditUserPanel() {

		editUserFrame = new JFrame("Edit gebruiker: " + user.getName());
		editUserFrame.setContentPane(new EditUserPanel(user, this));
		editUserFrame.pack();
		editUserFrame.setVisible(true);
	}

	public void closeFrame() {
		editUserFrame.dispose();
	}

	public void editUser(String username, char[] password, char[] newPassword, char[] retypePassword, String alias) {
		UserFileWriter userFileWriter = new UserFileWriter();

		if (password.length == 0) {
			JOptionPane.showMessageDialog(null, "Please enter your current password.",
				   "Error",
				   JOptionPane.ERROR_MESSAGE);
		} else if (!CryptoManager.checkPass(new String(password), user)) {
			JOptionPane.showMessageDialog(null, "Please enter the correct current password.",
				   "Error",
				   JOptionPane.ERROR_MESSAGE);
		} else if ("".equals(alias.trim())) {
			JOptionPane.showMessageDialog(null, "Please enter an alias.",
				   "Error",
				   JOptionPane.ERROR_MESSAGE);
		} else if (!new String(newPassword).equals(new String(retypePassword))) {
			JOptionPane.showMessageDialog(null, "The new password and the retype password do not match.",
				   "Error",
				   JOptionPane.ERROR_MESSAGE);
		} else {
			ArrayList<Friend> friends = abstractLoungeModel.getCurrentUser().getFriends();
			
			if (newPassword.length == 0 && retypePassword.length == 0) {
				user = new User(username, new String(password), alias, null, 0);				
			} else {
				user = new User(username, new String(newPassword), alias, null, 0);
			}
			
			user.getFriends().addAll(friends);
			
			userFileWriter.adjustUser(user);

			closeFrame();
			
			JOptionPane.showMessageDialog(null, "Profile edited",
				   "Edited",
				   JOptionPane.INFORMATION_MESSAGE);
			
			abstractLoungeModel.setCurrentUser(user);
			Chat.getSingleton().getChatTabbedModel().editChatter(user);
			
			for (Iterator<Friend> it = abstractLoungeModel.getCurrentUser().getFriends().iterator(); it.hasNext();) {
				Friend friend = it.next();
				NetworkAdapter.getSingleton().sendMessage(AbstractLoungeModel.NAME_CHANGE_TOKEN + " " +
					 alias, friend.getIp().getHostAddress(), friend.getName());
			}

		}
	}
}
