package userManagement;

import java.io.Serializable;
import java.text.SimpleDateFormat;
import java.util.GregorianCalendar;
import java.util.Locale;

/**
 * @author NVH
 * @filename HighScore.java
 */
public class HighScore implements Serializable {

	private int score;
	private GregorianCalendar date;
	private String game;

	public HighScore(int score, GregorianCalendar date, String game) {
		this.score = score;
		this.date = date;
		this.game = game;
	}

	@Override
	public String toString() {
		SimpleDateFormat date_format = new SimpleDateFormat("dd MMM yyyy HH:mm:ss", Locale.ENGLISH);
		return "Game: " + game + "\tScore: " + score + "\tDate: " + date_format.format(date.getTime());
	}

	public GregorianCalendar getDate() {
		return date;
	}

	public String getGame() {
		return game;
	}

	public int getScore() {
		return score;
	}
}
