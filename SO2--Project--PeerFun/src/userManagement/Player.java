/**
 *
 * @author Tom Naessens 
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */

package userManagement;

import java.net.InetAddress;

public class Player extends Friend implements PlayerInterface {

	private boolean isReady;
	private int teamId;
	
	public Player(String name, String alias, InetAddress IP) {
		super(name, alias, IP);
		
		teamId = 0;
		isReady = false;
	}

	public boolean isIsReady() {
		return isReady;
	}

	@Override
	public int getTeamId() {
		return teamId;
	}

	public void setIsReady(boolean isReady) {
		this.isReady = isReady;
	}

	public void setTeamId(int teamId) {
		this.teamId = teamId;
	}

	@Override
	public String getName() {
		return super.getName();
	}
	
	@Override
	public String getAlias() {
		return super.getAlias();
	}
	
}
