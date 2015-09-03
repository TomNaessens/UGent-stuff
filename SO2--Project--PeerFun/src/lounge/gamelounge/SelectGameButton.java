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

class SelectGameButton extends JButton implements ActionListener {

	GameLoungeModel gameLoungeModel;
	JList dataList;
	
	public SelectGameButton(GameLoungeModel gameLoungeModel, String choose, JList dataList) {
		super(choose);
		
		this.gameLoungeModel = gameLoungeModel;
		this.dataList = dataList;
		
		addActionListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		gameLoungeModel.pickGame((String) dataList.getSelectedValue());
	}

}
