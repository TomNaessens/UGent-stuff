package dammen;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;

import javax.swing.JPanel;


public class GUI extends JPanel{
	
	private Vak[][] matrix;
	
	public GUI(){
		super();
		setPreferredSize(new Dimension(500, 500));
		
		matrix = new Vak[10][10];
		int teamID = 1;
		for(int i = 0; i < 10; i++){
			for(int j = 0; j < 10; j++){
				if(i == 6) teamID = 2; 
				if(i % 2 == 0 && j % 2 == 1 && (i <= 3 || i >= 6)){
					matrix[i][j] = new Vak(j*50, i*50, true,teamID);
				}else if(i % 2 == 1 && j % 2 == 0 && (i <= 3 || i >= 6) ){
					matrix[i][j] = new Vak(j*50,i*50,true,teamID);
				}
				else{
					matrix[i][j] = new Vak(j*50,i*50,false,0);
				}
			}
		}
		}
		
	@Override 
	protected void paintComponent(Graphics g){
		super.paintComponent(g);
		for(int i = 0; i < 10; i++){
			for(int j = 0; j < 10; j++){
				if(i % 2 == 0 && j % 2 == 0)
					g.setColor(Color.WHITE);
				else if(i%2==1 && j % 2 == 1)
					g.setColor(Color.WHITE);
				else
					g.setColor(Color.BLACK);
			g.drawRect(j*50, i*50, 50, 50);
			g.fillRect(j*50, i*50, 50, 50);
			
			matrix[i][j].drawBlock(g);
			}
		}
	}
}
