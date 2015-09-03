/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Views.Ontwerper;

import elektrobank.Models.ModelBeheerder;
import java.awt.BorderLayout;
import javax.swing.JPanel;
import javax.swing.JScrollPane;

public class OntwerperTabPanel extends JPanel {

	public OntwerperTabPanel(ModelBeheerder mBeheerder) {

		setLayout(new BorderLayout());
		
		JPanel tekenPanel = new TekenPanel(mBeheerder);
		JPanel optiePanel = new OptiePanel(mBeheerder);

		JScrollPane tekenContainer = new JScrollPane(tekenPanel);

		add(tekenContainer,BorderLayout.CENTER);
		add(optiePanel,BorderLayout.EAST);
	}

}
