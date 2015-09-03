/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package minesweeper;

import java.awt.BorderLayout;
import javax.swing.JFrame;
import javax.swing.JPanel;

public class MineSweeper {
	
	public static void main(String[] args) {
		JFrame frame = new JFrame("Minesweeper");
		
		JPanel game = new JPanel(new BorderLayout());
		
		MineModel model = new MineModel();
		GamePanel panel = new GamePanel(model);
		
		frame.setContentPane(panel);
		
		model.setGamePanel(panel);		
		
		frame.pack();
		frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
		
		frame.setVisible(true);
	}
}
