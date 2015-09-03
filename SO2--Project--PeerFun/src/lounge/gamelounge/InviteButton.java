/**
 *
 * @author Tom Naessens 
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */

package lounge.gamelounge;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JButton;
import javax.swing.JList;
import lounge.gatheringlounge.FriendList;

class InviteButton extends JButton implements ActionListener {

	GameLoungeModel gameLoungeModel;
	JList playerJList;
	
	public InviteButton(GameLoungeModel gameLoungeModel, String invite, JList playerJList) {
		super(invite);
		this.gameLoungeModel = gameLoungeModel;
		this.playerJList = playerJList;
		
		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		gameLoungeModel.invitePlayers(playerJList);
	}

}
