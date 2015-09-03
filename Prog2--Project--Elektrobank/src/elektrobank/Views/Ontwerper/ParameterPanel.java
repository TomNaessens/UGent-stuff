/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Views.Ontwerper;

import elektrobank.Models.Ontwerper.ParameterModel;
import java.awt.Dimension;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

class ParameterPanel extends JPanel implements ChangeListener {

	ParameterModel pModel;

	public ParameterPanel(ParameterModel pModel) {
		setPreferredSize(new Dimension(200,100));

		this.pModel = pModel;
		
		pModel.addChangeListener(this);
	}

	public void stateChanged(ChangeEvent e) {
		removeAll();
		add(pModel.getSelectedComponent());
		repaint();
		revalidate();
	}

}
