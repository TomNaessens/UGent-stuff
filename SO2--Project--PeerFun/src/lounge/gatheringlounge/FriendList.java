/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gatheringlounge;

import java.util.Iterator;
import javax.swing.DefaultListModel;
import javax.swing.JList;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import lounge.AbstractLoungeModel;
import userManagement.Friend;

public class FriendList extends JList implements ChangeListener {

	AbstractLoungeModel abstractLoungeModel;
	DefaultListModel listModel;

	public FriendList(AbstractLoungeModel abstractLoungeModel, DefaultListModel listModel) {
		super(listModel);
		
		abstractLoungeModel.addChangeListener(this);

		this.abstractLoungeModel = abstractLoungeModel;
		this.listModel = listModel;
	}

	@Override
	public void stateChanged(ChangeEvent e) {
		
		listModel.clear();

		Iterator<Friend> iterator = abstractLoungeModel.getFriends().iterator();
		while (iterator.hasNext()) {
			listModel.addElement(iterator.next());
		}
		
		repaint();
		
	}
}