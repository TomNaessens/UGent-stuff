/**
 *
 * @author Tom Naessens 
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */

package lounge.gamelounge;

import java.awt.Color;
import javax.swing.BorderFactory;
import javax.swing.GroupLayout;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.border.TitledBorder;

class GameInfoPanel extends JPanel {

	public GameInfoPanel(GameLoungeModel gameLoungeModel) {
		
		setBorder(BorderFactory.createTitledBorder("Game info"));
		
		GroupLayout layout = new GroupLayout(this);
		
		JLabel gameNameLabel = new JLabel("Game name:");
		JLabel gameName = new GameNameLabel(gameLoungeModel, gameLoungeModel.getGameName());
		
		JLabel numberOfTeamsLabel = new JLabel("# teams:");
		JLabel numberOfTeams = new GameTeamsLabel(gameLoungeModel, Integer.toString(gameLoungeModel.getGameTeams()));
		
		JLabel numberOfPlayersLabel = new JLabel("# players (in total):");
		JLabel numberOfPlayers = new GamePlayersLabel(gameLoungeModel, Integer.toString(gameLoungeModel.getGamePlayers()));
		
		JScrollPane gameInfo = new JScrollPane(new GameDescriptionArea(gameLoungeModel, gameLoungeModel.getGameDescription()));
		
		JButton chooseGameButton = new ChooseGameButton(gameLoungeModel, "Choose game");
		JButton installGameButton = new InstallGameButton(gameLoungeModel, "Install game");
		
		layout.setAutoCreateGaps(true);
		
		layout.setVerticalGroup(
			   layout.createParallelGroup()
				.addGroup(layout.createSequentialGroup()
					.addGroup(layout.createParallelGroup()
						.addComponent(gameNameLabel)
						.addComponent(gameName)
					)
					.addGroup(layout.createParallelGroup()
						.addComponent(numberOfTeamsLabel)
						.addComponent(numberOfTeams)
					)
					.addGroup(layout.createParallelGroup()
						.addComponent(numberOfPlayersLabel)
						.addComponent(numberOfPlayers)
					)
					
					.addComponent(gameInfo)
					
					.addGroup(layout.createParallelGroup()
						.addComponent(chooseGameButton)
						.addComponent(installGameButton)
					)
			 )
		);
		
		layout.setHorizontalGroup(
			layout.createParallelGroup()
				.addGroup(layout.createSequentialGroup()
					.addGroup(layout.createParallelGroup()
						.addGroup(layout.createSequentialGroup()
							.addComponent(chooseGameButton)
							.addComponent(installGameButton)
						)
						.addComponent(gameInfo)
						.addGroup(layout.createSequentialGroup()
							.addComponent(numberOfTeamsLabel)
							.addComponent(numberOfTeams)
						)
						.addGroup(layout.createSequentialGroup()
							.addComponent(numberOfPlayersLabel)
							.addComponent(numberOfPlayers)
						)
						.addGroup(layout.createSequentialGroup()
							.addComponent(gameNameLabel)
							.addComponent(gameName)
						)
					)
				)
		);

			 
		setLayout(layout);
		
	}

}
