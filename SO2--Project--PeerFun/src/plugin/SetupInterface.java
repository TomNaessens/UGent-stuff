package plugin;
/**
 * We gebruiken deze klasse om een entry-point klasse te hebben in een 
 * boardgame. Deze interface heeft 1 methode die een boardgame terug heeft 
 * @param  		GameLoader
 * @return      Boardgame
 */
public interface SetupInterface {
	public BoardGame setup(GameLoader gameLoader);
	public String getNameGame();
	public String getGameDescription();
	public String getGameRules();
	public int getNumberofteams();
	public int getNumberofplayer();
}
