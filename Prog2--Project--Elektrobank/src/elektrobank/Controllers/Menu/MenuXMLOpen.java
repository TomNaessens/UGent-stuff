/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Controllers.Menu;

import elektrobank.Models.ModelBeheerder;
import elektrobank.utils.PointNode;
import elektrobank.utils.PointNodeConverter;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.io.File;
import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.JFileChooser;
import javax.swing.KeyStroke;
import javax.swing.filechooser.FileNameExtensionFilter;
import joldespice.circuit.ComponentCircuit;
import joldespice.circuit.EdgeCircuit;
import joldespice.components.Component;
import joldespice.components.SimpleNode;
import joldespice.util.xml.GraphMLImporter;
import joldespice.util.xml.converters.ComponentConverter;
import joldespice.util.xml.converters.ComponentConverter.ComponentDescriptionException;
import joldespice.util.xml.converters.ConverterException;
import org.jdom.JDOMException;
import org.jdom.input.JDOMParseException;

public class MenuXMLOpen extends AbstractAction {

	ModelBeheerder mBeheerder;
	JFileChooser fileChooser;
	GraphMLImporter<SimpleNode, Component, ComponentCircuit> importer;

	public MenuXMLOpen(ModelBeheerder mBeheerder, String title) {
		super(title);
		putValue(Action.ACCELERATOR_KEY, KeyStroke.getKeyStroke("control O"));
		putValue(Action.MNEMONIC_KEY, new Integer(KeyEvent.VK_O));

		this.mBeheerder = mBeheerder;
	}

	public void actionPerformed(ActionEvent e) {

		fileChooser = new JFileChooser();
		fileChooser.setFileFilter(new FileNameExtensionFilter("*.graphml", "graphml"));
		if (fileChooser.showOpenDialog(null) == JFileChooser.APPROVE_OPTION) {
			try {
				File f = fileChooser.getSelectedFile();
				importer = new GraphMLImporter(new PointNodeConverter(), new ComponentConverter(), EdgeCircuit.getFactory(PointNode.class));
				mBeheerder.getSelected().setCirc(importer.fromFile(f));
				mBeheerder.getSModel().resetSim();
				mBeheerder.getSModel().initSim();
				// Blijkbaar moeten we dit telkens opnieuw toevoegen, anders logt hij niet naar de juiste plaats
				Logger.getLogger("Elektrobank").setUseParentHandlers(false);
				Logger.getLogger("Elektrobank").addHandler(mBeheerder.getLoggerModel().getLogHandler());
				Logger.getLogger("Elektrobank").log(Level.INFO, "Bestand " + f.getName() + " geladen");
			} catch (JDOMParseException ex) {
				Logger.getLogger("Elektrobank").setUseParentHandlers(false);
				Logger.getLogger("Elektrobank").addHandler(mBeheerder.getLoggerModel().getLogHandler());
				Logger.getLogger("Elektrobank").log(Level.SEVERE, "Onbekende fout opgetreden");
			} catch (JDOMException ex) {
				Logger.getLogger("Elektrobank").setUseParentHandlers(false);
				Logger.getLogger("Elektrobank").addHandler(mBeheerder.getLoggerModel().getLogHandler());
				Logger.getLogger("Elektrobank").log(Level.SEVERE, "Onbekende fout opgetreden");
			} catch (IOException ex) {
				Logger.getLogger("Elektrobank").setUseParentHandlers(false);
				Logger.getLogger("Elektrobank").addHandler(mBeheerder.getLoggerModel().getLogHandler());
				Logger.getLogger("Elektrobank").log(Level.SEVERE, "Onbekende fout opgetreden");
			} catch (ComponentDescriptionException ex) {
				Logger.getLogger("Elektrobank").setUseParentHandlers(false);
				Logger.getLogger("Elektrobank").addHandler(mBeheerder.getLoggerModel().getLogHandler());
				Logger.getLogger("Elektrobank").log(Level.SEVERE, "Onbekende fout opgetreden");
			} catch (ConverterException ex) {
				Logger.getLogger("Elektrobank").setUseParentHandlers(false);
				Logger.getLogger("Elektrobank").addHandler(mBeheerder.getLoggerModel().getLogHandler());
				Logger.getLogger("Elektrobank").log(Level.SEVERE, "Onbekende fout opgetreden");
			} finally {
				// Bugfix: als er een leeg circuit werd ingelezen en er een node werd toegevoegd
				// kwam er een ArrayOutOfBoundsException
				if (mBeheerder.getSelected().getCirc().getNodes().length == 0) {
					mBeheerder.getSelected().clearAll();
				}
				mBeheerder.getSelected().updateDimension();
			}

		}
	}
}
