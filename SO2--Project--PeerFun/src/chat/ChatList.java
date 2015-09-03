/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package chat;

import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.Iterator;
import javax.swing.DefaultListModel;
import javax.swing.JList;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import userManagement.Friend;

public class ChatList extends JList implements ChangeListener, MouseListener {

	ChatModel chatModel;
	DefaultListModel listModel;

	public ChatList(ChatModel chatModel, DefaultListModel listModel) {
		super(listModel);

		this.chatModel = chatModel;
		this.listModel = listModel;

		chatModel.addChangeListener(this);
		addMouseListener(this);
	}

	@Override
	public void stateChanged(ChangeEvent e) {

		listModel.clear();

		Iterator<Friend> iterator = chatModel.getChatters().iterator();
		while (iterator.hasNext()) {
			listModel.addElement(iterator.next());
		}

		repaint();

	}

	@Override
	public void mouseClicked(MouseEvent e) {
		if (e.getClickCount() == 2) {
			int index = locationToIndex(e.getPoint());
			Friend friend = (Friend) getModel().getElementAt(index);
			ensureIndexIsVisible(index);

			Chat.getSingleton().addChat(friend.getAlias());
			Chat.getSingleton().addChatter(friend.getAlias(), friend);
		}
	}

	@Override
	public void mousePressed(MouseEvent e) {
	}

	@Override
	public void mouseReleased(MouseEvent e) {
	}

	@Override
	public void mouseEntered(MouseEvent e) {
	}

	@Override
	public void mouseExited(MouseEvent e) {
	}
}