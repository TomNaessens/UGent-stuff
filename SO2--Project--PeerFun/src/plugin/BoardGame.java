
package plugin;

import javax.swing.JPanel;

import userManagement.PlayerInterface;

public abstract class BoardGame{
	
    protected GameLoader loader;
	protected String name;
	protected int numberOfPlayers;
	protected int numberOfTeams;

	public BoardGame(GameLoader loader)
    {
        this.loader = loader;
    }
	public abstract void update(GameState gameState, PlayerInterface Player);
	public abstract void playerLeft(PlayerInterface player);
	public abstract JPanel getPaneel();
	
	
}
