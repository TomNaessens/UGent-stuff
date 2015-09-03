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

public class GameListPanel extends JPanel {
	
	public GameListPanel(GameLoungeModel gameLoungeModel, JList dataList) {
		
		GroupLayout layout = new GroupLayout(this);
		layout.setAutoCreateContainerGaps(true);
		
		JScrollPane scrollPane = new JScrollPane(dataList);
		
		JButton selectGameButton = new SelectGameButton(gameLoungeModel, "Choose", dataList);

		layout.setHorizontalGroup(
			layout.createParallelGroup()
				.addComponent(scrollPane)
				.addComponent(selectGameButton)
		);

		layout.setVerticalGroup(
			layout.createSequentialGroup()
				.addComponent(scrollPane)
				.addComponent(selectGameButton)
		);
		
		setLayout(layout);
	}

}
