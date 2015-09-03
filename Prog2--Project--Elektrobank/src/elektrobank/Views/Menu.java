/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Views;

import elektrobank.Controllers.Handlers.MouseHandler;
import elektrobank.Controllers.Menu.MenuBoodschappenAction;
import elektrobank.Controllers.Menu.MenuLoopButton;
import elektrobank.Controllers.Menu.MenuSelectedActionController;
import elektrobank.Controllers.Menu.MenuSelectedComponentController;
import elektrobank.Controllers.Menu.MenuNewCircuitAction;
import elektrobank.Models.Ontwerper.TekenModel;
import elektrobank.Models.ModelBeheerder;
import elektrobank.Models.Ontwerper.SelectedActionModel;
import elektrobank.Models.Ontwerper.SelectedComponentModel;
import elektrobank.icons.IconPainter;
import elektrobank.Controllers.Menu.MenuXMLOpen;
import elektrobank.Controllers.Menu.MenuXMLSave;
import elektrobank.Models.Simulator.SimulatorModel;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JPopupMenu.Separator;

public class Menu extends JMenuBar {

	SelectedActionModel saModel;
	TekenModel tModel;
	SelectedComponentModel scModel;
	SimulatorModel sModel;

	public Menu(JFrame logger, ModelBeheerder mBeheerder) {

		saModel = mBeheerder.getSAModel();
		tModel = mBeheerder.getTModel();
		scModel = mBeheerder.getSCModel();
		sModel = mBeheerder.getSModel();

		// Bestand submenu
		JMenu categoryBestand = new JMenu("Bestand");
		categoryBestand.add(new MenuBoodschappenAction(logger, "Boodschappen"));
		categoryBestand.add(new MenuNewCircuitAction(mBeheerder, "Nieuw"));
		categoryBestand.add(new MenuXMLOpen(mBeheerder, "GraphML openen"));
		categoryBestand.add(new MenuXMLSave(mBeheerder, "GraphML opslaan"));
		add(categoryBestand);

		// Ontwerp submenu
		JMenu categoryOntwerp = new JMenu("Ontwerp");

		MouseHandler[] listeners = saModel.getListeners();
		String[] captions = saModel.getCAPTIONS();
		for (int i = 0; i < listeners.length; i++) {
			categoryOntwerp.add(new MenuSelectedActionController(saModel, captions[i], listeners[i]));
		}

		categoryOntwerp.add(new Separator());

		JMenu componenten = new JMenu("Componenten");
		IconPainter[] icons = scModel.getICONLIST();
		String[] iconNames = scModel.getIconNames();
		for (int i = 0; i < icons.length; i++) {
			componenten.add(new MenuSelectedComponentController(mBeheerder, iconNames[i], icons[i]));
		}

		categoryOntwerp.add(componenten);

		add(categoryOntwerp);

		// Simuleer submenu
		JMenu simuleerCategory = new JMenu("Simuleer");

		JMenuItem stepSimulatieItem = new JMenuItem("Stap simulatie");
		stepSimulatieItem.addActionListener(new ActionListener() {

			public void actionPerformed(ActionEvent e) {
				sModel.doStep();
			}
		});
		simuleerCategory.add(stepSimulatieItem);

		simuleerCategory.add(new MenuLoopButton(mBeheerder.getSModel(), "Loop simulatie"));

		JMenuItem resetSimulatieItem = new JMenuItem("Reset simulatie");
		resetSimulatieItem.addActionListener(new ActionListener() {

			public void actionPerformed(ActionEvent e) {
				sModel.resetSim();
			}
		});
		simuleerCategory.add(resetSimulatieItem);

		add(simuleerCategory);
	}
}
