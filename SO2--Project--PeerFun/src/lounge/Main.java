package lounge;

import java.awt.BorderLayout;
import java.awt.EventQueue;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.UIManager;
import lounge.startscreen.StartScreen;
import lounge.startscreen.StartScreenModel;
import network.NetworkAdapter;

public class Main {

	public static void main(String[] args) {

		// Mooie stijl is mooi
		try {
			UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
		} catch (Exception e) {
		}

		// Init frame & panel
		EventQueue.invokeLater(new Runnable() {

			@Override
			public void run() {

				JFrame window = new JFrame("Het Dieter-Sander-Nick-Tom-Episch-Framework");

				JPanel panel = new JPanel(new BorderLayout());

				StartScreenModel startScreenModel = new StartScreenModel(window);
				panel.add(new StartScreen(startScreenModel));

				window.add(panel);
				window.pack();

				window.setDefaultCloseOperation(JFrame.DO_NOTHING_ON_CLOSE); // Override voor bevestiging:

				window.addWindowListener(new LoungeWindowAdapter());
				window.setVisible(true);
			}
		});
	}
}