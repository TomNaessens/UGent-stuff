/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Views.Ontwerper.ParameterPanels;

import javax.swing.BorderFactory;
import javax.swing.GroupLayout;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextField;

public class SingleParameterPanel extends JPanel {

	public SingleParameterPanel(String titel, JTextField field, String label) {

		JPanel tempPanel = new JPanel();

		GroupLayout layout = new GroupLayout(tempPanel);

		tempPanel.setLayout(layout);
//		tempPanel.setBorder(BorderFactory.createTitledBorder(titel));

		JLabel title = new JLabel(titel);
		JLabel afkorting = new JLabel(label);

		layout.setVerticalGroup(
			   layout.createSequentialGroup()
			   .addComponent(title)
			   .addGroup(layout.createParallelGroup()
				.addComponent(field)
				.addComponent(afkorting, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
			   )
		);

		layout.setHorizontalGroup(
			   layout.createParallelGroup()
			   .addComponent(title)
			   .addGroup(layout.createSequentialGroup()
				.addComponent(field)
				.addComponent(afkorting, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				)
			   );
		
		add(tempPanel);

	}
}
