/**
 *
 * @author Tom Naessens 
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */

package chat;

import java.util.Comparator;
import userManagement.Friend;

public class CompareByAlias implements Comparator<Friend> {

	@Override
	public int compare(Friend t, Friend t1) {
		return t.getAlias().compareTo(t1.getAlias());
	}
	
}
