package plugin;

import java.awt.EventQueue;
import java.awt.event.ActionListener;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.EventObject;
import java.util.HashMap;

import javax.swing.event.ChangeEvent;


public class GameStep extends ChangeEvent {

	private MouseEvent e;
	private String info;
	
	public GameStep(GameState gameState) {
		super(gameState);
	}

	private String indentifier;
	
	/**getters en setters*/
	public String getIdentifier(){ return indentifier; }

	public void setInfo(String info) {
		// TODO Auto-generated method stub
		this.info = info;
	}
	
	public void setMouseEven(MouseEvent e){
		this.e = e;
	}
	public MouseEvent getMouseEvent(){ return e; }
	
	public String getInfo(){return info; }

	public void assemble() {
		
	}
}
