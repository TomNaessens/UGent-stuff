/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gatheringlounge;

import java.awt.Component;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.ListCellRenderer;
import userManagement.Friend;

public class FriendListRenderer extends JLabel implements ListCellRenderer {

	@Override
	public Component getListCellRendererComponent(JList list, Object value,
		 int index, boolean isSelected, boolean cellHasFocus) {

		Friend friend = (Friend) value;

		if (isSelected) {
			setBackground(list.getSelectionBackground());
			setForeground(list.getSelectionForeground());
		} else {
			setBackground(list.getBackground());
			setForeground(list.getForeground());
		}

		SquareIcon icon = new SquareIcon(friend.getStatus().getColor(), 10, getHorizontalAlignment(), 10, 10);
		setOpaque(true);
		
		setText(friend.getAlias());
		
		setIcon(icon);
		setIconTextGap(15);

		return this;

	}
}
