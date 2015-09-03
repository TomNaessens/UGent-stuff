/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Views.Ontwerper;

import elektrobank.Controllers.Buttons.SelectedComponentController;
import elektrobank.Models.Ontwerper.ParameterModel;
import elektrobank.Models.Ontwerper.SelectedComponentModel;
import elektrobank.icons.IconPainter;
import java.awt.Dimension;
import java.awt.GridLayout;
import javax.swing.JPanel;

class ComponentenPanel extends JPanel {

	public ComponentenPanel(SelectedComponentModel scModel, ParameterModel pModel) {

		setPreferredSize(new Dimension(200,200));
		setLayout(new GridLayout(5,2));

		IconPainter[] iconList = SelectedComponentModel.getICONLIST();
		
		for(int i = 0; i < iconList.length; i++) {
			add(new SelectedComponentController(scModel, pModel, iconList[i]));
		}
		
	}

}
