/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package userManagement;

import java.util.Comparator;

public class HighScoreComparator implements Comparator<HighScore> {

	@Override
	public int compare(HighScore t, HighScore t1) {
		
		if(!t.getGame().equals(t1.getGame())) {
			return t.getGame().compareTo(t1.getGame());
		} else {
			return t1.getScore() - t.getScore();
		}
	}

}
