/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank;

import elektrobank.Controllers.Logger.ChangeList;
import elektrobank.Models.Logger.LoggerModel;
import elektrobank.Models.ModelBeheerder;
import elektrobank.Views.Logger.LoggerPanel;
import java.awt.BorderLayout;
import javax.swing.JFrame;
import javax.swing.JPanel;
import elektrobank.Views.Menu;
import elektrobank.Views.TabbedPanel;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.util.logging.Logger;
import javax.swing.DefaultListModel;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.UIManager;

public class Elektrobank extends JFrame {

	public static void main(String[] args) {
		// Initialisatie loggers
		DefaultListModel logListModel = new DefaultListModel();
		LoggerModel lModel = new LoggerModel(logListModel);

		ChangeList boodschappen = new ChangeList(lModel, logListModel);

		Logger.getLogger("Elektrobank").addHandler(lModel.getLogHandler());
		Logger.getLogger("Elektrobank").setUseParentHandlers(false);

		joldespice.JOldeSpice.LOGGER.addHandler(lModel.getLogHandler());
		joldespice.JOldeSpice.LOGGER.setUseParentHandlers(false);

		// Modelbeheerder wordt aangemaakt
		ModelBeheerder mBeheerder = new ModelBeheerder();
		mBeheerder.setLogListModel(logListModel);
		mBeheerder.setlModel(lModel);

		// Logger GUI
		JFrame logger = new JFrame("Logger");
		logger.setContentPane(new LoggerPanel(mBeheerder, boodschappen));
		logger.pack();
		logger.setVisible(false);
		logger.setDefaultCloseOperation(JFrame.HIDE_ON_CLOSE);


		// GUI
		JFrame window = new JFrame("Elektrobank");

		JPanel panel = new JPanel(new BorderLayout());

		panel.add(new Menu(logger, mBeheerder), BorderLayout.NORTH);
		panel.add(new TabbedPanel(mBeheerder), BorderLayout.CENTER);

		window.add(panel);

		window.pack();
		window.setDefaultCloseOperation(JFrame.DO_NOTHING_ON_CLOSE);
		window.addWindowListener(new WindowAdapter() {

			@Override
			public void windowClosing(WindowEvent e) {
				int confirmed = JOptionPane.showConfirmDialog(null,
					   "Are you sure you want to exit?\nIf you close now, you will lose all unsaved work.", "Warning",
					   JOptionPane.YES_NO_OPTION, JOptionPane.QUESTION_MESSAGE, null);
				if (confirmed == JOptionPane.YES_OPTION) {

					System.exit(0);
				}
			}
		});
		window.setVisible(true);

	}
}
