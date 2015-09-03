/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gamelounge;

import java.awt.Component;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.ListCellRenderer;
import lounge.gatheringlounge.SquareIcon;
import userManagement.Player;

public class FriendTeamListRenderer extends JLabel implements ListCellRenderer {

	GameLoungeModel gameLoungeModel;

	public FriendTeamListRenderer(GameLoungeModel gameLoungeModel) {
		this.gameLoungeModel = gameLoungeModel;
	}

	@Override
	public Component getListCellRendererComponent(JList list, Object value,
		 int index, boolean isSelected, boolean cellHasFocus) {

		Player player = (Player) value;

		if (isSelected) {
			setBackground(list.getSelectionBackground());
			setForeground(list.getSelectionForeground());
		} else {
			setBackground(list.getBackground());
			setForeground(list.getForeground());
		}

		setOpaque(true);

		SquareIcon icon = new SquareIcon(player.getStatus().getColor(), 10, getHorizontalAlignment(), 10, 10);
		String text = "";


		if (player.getTeamId() == 0) {
			text += "?";
		} else {
			text += player.getTeamId();
		}

		text += " - ";

		text += player.getAlias();

		setIcon(icon);
		setIconTextGap(15);
		setText(text);

		return this;

	}
}
