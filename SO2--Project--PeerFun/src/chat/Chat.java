/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package chat;

public class Chat {

	private static ChatTabbedPanel SINGLETON;

	public static ChatTabbedPanel getSingleton() {
		if (SINGLETON == null) {
			SINGLETON = new ChatTabbedPanel();
		}
		return SINGLETON;
	}
}
