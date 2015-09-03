/**
 *
 * @author Tom Naessens 
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */

package lounge.gamelounge;

import javax.swing.GroupLayout;
import javax.swing.JButton;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;

class InvitePanel extends JPanel {
	
	public InvitePanel(GameLoungeModel gameLoungeModel, JList friendJList) {
		
		GroupLayout layout = new GroupLayout(this);
		layout.setAutoCreateContainerGaps(true);
		
		JScrollPane scrollPane = new JScrollPane(friendJList);
		
		JButton inviteButton = new InviteButton(gameLoungeModel, "Invite", friendJList);

		layout.setHorizontalGroup(
			layout.createParallelGroup()
				.addComponent(scrollPane)
				.addComponent(inviteButton)
		);

		layout.setVerticalGroup(
			layout.createSequentialGroup()
				.addComponent(scrollPane)
				.addComponent(inviteButton)
		);
		
		setLayout(layout);
	}

}
