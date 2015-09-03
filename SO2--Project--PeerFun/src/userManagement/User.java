package userManagement;

import fileInteraction.UserFileWriter;
import java.io.Serializable;
import java.net.InetAddress;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.GregorianCalendar;
import java.util.List;
import java.util.Locale;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * @author NVH 
 * @filename User.java
 */
public class User extends Player implements Serializable, UserInterface {

	private String hashPassWord;
	private List<HighScore> highScores;
	private ArrayList<Friend> friends;

	public User(String userName, String password, String alias, InetAddress ip, int port) {
		super(userName, alias, ip);
		highScores = new ArrayList<HighScore>();
		friends = new ArrayList<Friend>();

		try {
			hashPassWord = CryptoManager.byteArrayToHexString(CryptoManager.computeHash(password));
		} catch (Exception ex) {
			Logger.getLogger(User.class.getName()).log(Level.SEVERE, "Password encryption failed", ex);
		}
	}

	@Override
	public String showHighScores() {
		String string = "";
		for (HighScore highscore : highScores) {
			string += highscore;
			string += "\n";
		}
		return string;
	}

	
	public List<HighScore> getHighScores() {
		return highScores;
	}
	
	@Override
	public void addHighScore(int score, GregorianCalendar date, String game) {
		addHighScore(new HighScore(score, date, game));
	}
	
	@Override
	public void addHighScore(HighScore highScore) {
		highScores.add(highScore);
		
		Collections.sort(highScores, new HighScoreComparator());
		
		UserFileWriter userFileWriter = new UserFileWriter();
		userFileWriter.adjustUser(this);
	}

	@Override
	public String toString() {
		SimpleDateFormat date_format = new SimpleDateFormat("dd MMM yyyy", Locale.ENGLISH);
		String string = super.toString();
		string += "\n";
		string += "Alias: " + getAlias();
		return string;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final User other = (User) obj;
		if ((this.getName() == null) ? (other.getName() != null) : !this.getName().equals(other.getName())) {
			return false;
		}
		return true;
	}

	@Override
	public String getHashPassWord() {
		return hashPassWord;
	}
	
	public void addFriend(Friend friend) {
		friends.add(friend);
	}
	
	@Override
	public ArrayList<Friend> getFriends() {
		return friends;
	}
}
