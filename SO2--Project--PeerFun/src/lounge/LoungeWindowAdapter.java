/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge;

import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;
import javax.swing.JOptionPane;
import network.NetworkAdapter;

public class LoungeWindowAdapter implements WindowListener {

	AbstractLoungeModel abstractLoungeModel;

	public LoungeWindowAdapter() {
		abstractLoungeModel = null;
	}

	public void setAbstractLoungeModel(AbstractLoungeModel abstractLoungeModel) {
		this.abstractLoungeModel = abstractLoungeModel;
	}

	@Override
	public void windowOpened(WindowEvent e) {
	}

	@Override
	public void windowClosing(WindowEvent e) {
		int confirmed = JOptionPane.showConfirmDialog(null,
			 "Are you sure you want to exit?", "Warning",
			 JOptionPane.YES_NO_OPTION, JOptionPane.QUESTION_MESSAGE, null);
		
		if (confirmed == JOptionPane.YES_OPTION) {
			if(abstractLoungeModel != null) {
				abstractLoungeModel.windowClosed();
			}
			
			NetworkAdapter.getSingleton().stopHosting();

			System.exit(0);
		}
	}

	@Override
	public void windowClosed(WindowEvent e) {
	}

	@Override
	public void windowIconified(WindowEvent e) {
	}

	@Override
	public void windowDeiconified(WindowEvent e) {
	}

	@Override
	public void windowActivated(WindowEvent e) {
	}

	@Override
	public void windowDeactivated(WindowEvent e) {
	}
}
