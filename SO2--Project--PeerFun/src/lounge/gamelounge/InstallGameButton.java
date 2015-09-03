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

class InstallGameButton extends JButton implements ActionListener {

	GameLoungeModel gameLoungeModel;
	
	public InstallGameButton(GameLoungeModel gameLoungeModel, String install_game) {
		super(install_game);
		
		this.gameLoungeModel = gameLoungeModel;
		
		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		gameLoungeModel.installGame();
	}

}
