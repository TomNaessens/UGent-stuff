package dammen;

import java.awt.Color;
import java.awt.Graphics;
import java.awt.Graphics2D;

public class Vak {
	private int teamID;
	private int upperX;
	private int upperY;
	private boolean taken;
	private Color kleur;
	public Vak(int upperX, int upperY, boolean taken,
			int teamID){
		this.upperX = upperX;
		this.upperY = upperY;
		this.taken = taken;
		this.teamID = teamID;
	}
	
	
	public void drawBlock(Graphics g){
		if(taken){
			if(teamID == 1) kleur = Color.LIGHT_GRAY;
			else kleur = Color.DARK_GRAY;
			//dit vakje is bezet
			Graphics2D g2 = (Graphics2D)g.create();
			g2.setColor(kleur);
			g2.drawOval(upperX, upperY, 25*2, 25*2);
			g2.fillOval(upperX, upperY, 25*2, 25*2);
		}
	}
}
