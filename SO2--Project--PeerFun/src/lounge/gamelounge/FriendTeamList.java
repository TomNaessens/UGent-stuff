/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gamelounge;

import java.util.Iterator;
import javax.swing.DefaultListModel;
import javax.swing.JList;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import userManagement.Player;

public class FriendTeamList extends JList implements ChangeListener {

	GameLoungeModel gameLoungeModel;
	DefaultListModel listModel;

	public FriendTeamList(GameLoungeModel gameLoungeModel, DefaultListModel listModel) {
		super(listModel);
		
		gameLoungeModel.addChangeListener(this);

		this.gameLoungeModel = gameLoungeModel;
		this.listModel = listModel;
	}

	@Override
	public void stateChanged(ChangeEvent e) {
		
		listModel.clear();

		Iterator<Player> iterator = gameLoungeModel.getPlayers().iterator();
		while (iterator.hasNext()) {
			listModel.addElement(iterator.next());
		}
		
		repaint();
		
	}
}