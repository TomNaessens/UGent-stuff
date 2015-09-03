
import javax.swing.JFrame;

public class Main {

	public static void main(String[] args) {
		MyLTiles mlt = new MyLTiles();
		int k = 7;
		//Random rd = new Random();
		//int n = (int) Math.pow(2, k);
		int[][] solution = mlt.tile(k, 0, 0);
		JFrame frame = new JFrame("Taak 2");
		frame.setContentPane(new TilePanel(solution));
		frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		frame.pack();
		frame.setVisible(true);
	}
}
