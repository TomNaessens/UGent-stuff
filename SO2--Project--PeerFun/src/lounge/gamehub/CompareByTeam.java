/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gamehub;

import java.util.Comparator;
import userManagement.Player;

public class CompareByTeam implements Comparator<Player> {

	@Override
	public int compare(Player t, Player t1) {
		if (t.getTeamId() != t1.getTeamId()) {
			return t.getTeamId() - t1.getTeamId();
		} else {
			return t.getAlias().compareTo(t1.getAlias());
		}
	}
}
