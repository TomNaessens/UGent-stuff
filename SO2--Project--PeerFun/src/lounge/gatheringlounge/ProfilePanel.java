/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gatheringlounge;

import java.util.ArrayList;
import javax.swing.GroupLayout;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

public class ProfilePanel extends JPanel {

	public ProfilePanel(String playerName, String playerAlias, String playerScore) {

		JLabel playerNameLabel = new JLabel("Name:");
		JLabel name = new JLabel(playerName);

		JLabel playerAliasLabel = new JLabel("Alias:");
		JLabel alias = new JLabel(playerAlias);


		JTextArea textArea = new JTextArea(10, 40);
		textArea.setLineWrap(true);
		textArea.setEditable(false);
		if (playerScore.equals("")) {
			textArea.setText("No highscores found!");
		} else {
			textArea.setText(playerScore);
		}

		JScrollPane scores = new JScrollPane(textArea);


		GroupLayout layout = new GroupLayout(this);
		layout.setAutoCreateGaps(true);

		layout.setVerticalGroup(
			 layout.createParallelGroup().addGroup(layout.createSequentialGroup().addGroup(layout.createParallelGroup().addComponent(playerNameLabel).addComponent(name)).addGroup(layout.createParallelGroup().addComponent(playerAliasLabel).addComponent(alias)).addComponent(scores)));

		layout.setHorizontalGroup(
			 layout.createParallelGroup().addGroup(layout.createSequentialGroup().addGroup(layout.createParallelGroup().addComponent(scores).addGroup(layout.createSequentialGroup().addComponent(playerNameLabel).addComponent(name)).addGroup(layout.createSequentialGroup().addComponent(playerAliasLabel).addComponent(alias)))));

		setLayout(layout);

	}
}
