/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.startscreen;

import fileInteraction.UserExistsException;
import fileInteraction.UserFileReader;
import fileInteraction.UserFileWriter;
import java.net.InetAddress;
import java.net.UnknownHostException;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import lounge.gatheringlounge.GatheringLoungeModel;
import lounge.gatheringlounge.GatheringLoungePanel;
import lounge.misc.Model;
import userManagement.CryptoManager;
import userManagement.User;

public class StartScreenModel extends Model {

	String userName;
	String password;
	JFrame registerFrame;
	JFrame window;
	User currentUser;

	public StartScreenModel(JFrame window) {
		this.window = window;
		currentUser = null;
	}

	void openRegisterPanel(String userName, char[] password) {
		registerFrame = new JFrame("Register");
		RegisterPanel registerPanel = new RegisterPanel(this, userName.trim(), password);
		registerFrame.setContentPane(registerPanel);
		registerFrame.pack();
		registerFrame.setVisible(true);
	}

	public void registerAccount(String userName, char[] password, String realName) {

		if (userName.trim().isEmpty()) {
			JOptionPane.showMessageDialog(null, "Please enter a username.",
				 "Error",
				 JOptionPane.ERROR_MESSAGE);
		} else if (password.length == 0) {
			JOptionPane.showMessageDialog(null, "Please enter a password.",
				 "Error",
				 JOptionPane.ERROR_MESSAGE);
		} else if (realName.trim().isEmpty()) {
			JOptionPane.showMessageDialog(null, "Please enter an alias.",
				 "Error",
				 JOptionPane.ERROR_MESSAGE);
		} else {
			this.userName = userName.trim();
			this.password = new String(password);

			createUser(realName.trim());
		}
	}

	public void login(String userName, char[] password) {
		this.userName = userName;
		this.password = new String(password);

		UserFileReader userFileReader = new UserFileReader();
		User user = userFileReader.readUser(userName);

		if (user == null) {
			int choice = JOptionPane.showConfirmDialog(null,
				 "User does not exist, create new account?", "User not found",
				 JOptionPane.YES_NO_OPTION, JOptionPane.QUESTION_MESSAGE, null);
			if (choice == JOptionPane.YES_OPTION) {
				openRegisterPanel(userName, password);
			}

		} else {
			if (CryptoManager.checkPass(new String(password), user)) {
				currentUser = user;

				GatheringLoungeModel gatheringLoungeModel = new GatheringLoungeModel(window, currentUser);
				GatheringLoungePanel gatheringLoungePanel = new GatheringLoungePanel(gatheringLoungeModel);
		
				window.setContentPane(gatheringLoungePanel);
				window.pack();
			} else {
				JOptionPane.showMessageDialog(null, "The password does not match the usernames password",
					 "Error",
					 JOptionPane.ERROR_MESSAGE);
			}
		}
	}

	public void createUser(String alias) {
		UserFileWriter userFileWriter = new UserFileWriter();

		try {
			User user = null;
			try {
				user = new User(userName, password, alias, InetAddress.getLocalHost(), 0);
				System.out.println(InetAddress.getLocalHost().getHostAddress());
			} catch (UnknownHostException ex) {
			}
			userFileWriter.addNewUser(user);

			registerFrame.dispose();

			JOptionPane.showMessageDialog(null, "The account is created, you can now log in.",
				 "Account created",
				 JOptionPane.INFORMATION_MESSAGE);

		} catch (UserExistsException ex) {

			JOptionPane.showMessageDialog(null, "A user with that nickname already exists.",
				 "Error",
				 JOptionPane.INFORMATION_MESSAGE);

		}
	}

	public User getCurrentUser() {
		return currentUser;
	}
}
