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
import elektrobank.Models.Ontwerper.TekenModel;
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
import javax.swing.JOptionPane;
import javax.swing.KeyStroke;
import joldespice.components.Component;
import joldespice.util.xml.GraphMLExporter;
import joldespice.util.xml.converters.ComponentConverter;
import joldespice.util.xml.converters.ComponentConverter.ComponentDescriptionException;
import joldespice.util.xml.converters.ConverterException;

public class MenuXMLSave extends AbstractAction {

	TekenModel tModel;
	JFileChooser fileChooser;
	File file;
	GraphMLExporter<PointNode, Component> exporter;
	ModelBeheerder mBeheerder;

	public MenuXMLSave(ModelBeheerder mBeheerder, String title) {
		super(title);
		putValue(Action.ACCELERATOR_KEY, KeyStroke.getKeyStroke("control S"));
		putValue(Action.MNEMONIC_KEY, new Integer(KeyEvent.VK_S));

		this.tModel = mBeheerder.getTModel();
		this.mBeheerder = mBeheerder;
	}

	public void actionPerformed(ActionEvent e) {


		try {
			fileChooser = new JFileChooser();
			fileChooser.setSelectedFile(new File("untitled.graphml"));
			if (fileChooser.showSaveDialog(fileChooser) == JFileChooser.APPROVE_OPTION) {
				file = fileChooser.getSelectedFile();
				if (file.exists()) {
					if (JOptionPane.showOptionDialog(null, "Dit bestand bestaat al, wilt u het overschrijven?", "Opgelet", JOptionPane.YES_NO_OPTION, JOptionPane.QUESTION_MESSAGE, null, null, null) != JOptionPane.YES_OPTION) {
						return; // We willen de file niet overschrijven, dus ga uit de methode
					}
				}
				exporter = new GraphMLExporter<PointNode, Component>(new PointNodeConverter(), new ComponentConverter());
				exporter.toFile(file, mBeheerder.getSelected().getCirc());
				Logger.getLogger("Elektrobank").setUseParentHandlers(false);
				Logger.getLogger("Elektrobank").addHandler(mBeheerder.getLoggerModel().getLogHandler());
				Logger.getLogger("Elektrobank").log(Level.INFO, "Circuit opgeslagen onder de naam " + file.getName());
			}
		} catch (ComponentDescriptionException ex) {
			Logger.getLogger("Elektrobank").log(Level.SEVERE, "Onbekende fout opgetreden", ex);
		} catch (ConverterException ex) {
			Logger.getLogger("Elektrobank").log(Level.SEVERE, "Onbekende fout opgetreden", ex);
		} catch (IOException ex) {
			Logger.getLogger("Elektrobank").log(Level.SEVERE, "Onbekende fout opgetreden", ex);
		}
	}
}
