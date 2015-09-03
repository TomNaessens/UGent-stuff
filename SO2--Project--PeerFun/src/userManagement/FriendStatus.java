package userManagement;

import java.awt.Color;

/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
public enum FriendStatus {

	OFFLINE(192, 192, 192),
	READY(0, 201, 87),
	IN_GATHERINGLOUNGE(255, 215, 0),
	IN_GAMELOUNGE(255, 165, 0),
	IS_HOSTING(131, 111, 255),
	IN_GAME(255, 69, 0);
	
	Color color;

	FriendStatus(int r, int g, int b) {
		this.color = new Color(r, g, b);
	}

	public Color getColor() {
		return color;
	}
}
