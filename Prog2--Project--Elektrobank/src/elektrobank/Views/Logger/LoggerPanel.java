/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Views.Logger;

import elektrobank.Controllers.Logger.ChangeList;
import elektrobank.Controllers.Logger.LoggerLevelChanged;
import elektrobank.Controllers.Logger.ShowLoggerCheckBox;
import elektrobank.Models.ModelBeheerder;
import java.awt.Dimension;
import java.util.logging.Level;
import javax.swing.DefaultComboBoxModel;
import javax.swing.GroupLayout;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;

public class LoggerPanel extends JPanel {

	public LoggerPanel(ModelBeheerder mBeheerder, ChangeList boodschappen) {
		GroupLayout layout = new GroupLayout(this);
		setLayout(layout);
		layout.setAutoCreateContainerGaps(true);


		JCheckBox jOldeSpice = new ShowLoggerCheckBox(mBeheerder.getLoggerModel(), "jOldeSpice");
		JCheckBox elektrobank = new ShowLoggerCheckBox(mBeheerder.getLoggerModel(), "Elektrobank");

		JLabel level = new JLabel("Minimum level:");

		DefaultComboBoxModel levelBoxModel = new DefaultComboBoxModel(mBeheerder.getLoggerModel().getLevels());
		levelBoxModel.setSelectedItem(Level.ALL);
		JComboBox levelComboBox = new JComboBox(levelBoxModel);
		levelComboBox.addActionListener(new LoggerLevelChanged(mBeheerder.getLoggerModel()));

		JScrollPane scrollPane = new JScrollPane(boodschappen);
		scrollPane.setPreferredSize(new Dimension(600, 200));

		layout.setHorizontalGroup(
			   layout.createParallelGroup()
			   .addGroup(layout.createSequentialGroup()
					.addGroup(layout.createParallelGroup()
						.addComponent(jOldeSpice)
						.addComponent(elektrobank)
					)
					// Zorgt voor toch iets van ruimte tussen de checkboxes en de combobox
					.addContainerGap(30, 30)
					.addGroup(layout.createParallelGroup()
						.addComponent(level)
						.addComponent(levelComboBox)
					)
			    )
			    .addComponent(scrollPane)
		);

		layout.setVerticalGroup(
			   layout.createSequentialGroup()
					.addGroup(layout.createParallelGroup(GroupLayout.Alignment.BASELINE, false)
						.addGroup(layout.createSequentialGroup()
							.addComponent(jOldeSpice)
							.addComponent(elektrobank)
						)
					.addGroup(layout.createSequentialGroup()
						.addComponent(level)
						.addComponent(levelComboBox)
					)
					 )
			   .addComponent(scrollPane)
		);

	}
}
