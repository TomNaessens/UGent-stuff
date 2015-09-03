/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Controllers;

import elektrobank.Models.ModelBeheerder;
import elektrobank.Models.Ontwerper.ParameterModel;
import java.awt.AWTEvent;
import java.awt.Event;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;
import java.text.DecimalFormat;
import java.text.Format;
import java.util.HashMap;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.swing.JOptionPane;
import javax.swing.JTextField;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class ParameterTextField extends JTextField implements ActionListener, FocusListener, ChangeListener {

	private ModelBeheerder mBeheerder;
	private ParameterModel pModel;
	private int index;
	private HashMap<Character, Double> rescaleMap;
	private String oldValue;

	public ParameterTextField(ModelBeheerder mBeheerder, int index) {
		super(mBeheerder.getPModel().getTextFieldLength());

		this.mBeheerder = mBeheerder;
		this.pModel = mBeheerder.getPModel();

		this.index = index;

		rescaleMap = new HashMap<Character, Double>();
		rescaleMap.put('G', 1e9);
		rescaleMap.put('M', 1e6);
		rescaleMap.put('k', 1e3);
		rescaleMap.put('m', 1e-3);
		rescaleMap.put('µ', 1e-6);
		rescaleMap.put('n', 1e-9);
		rescaleMap.put('p', 1e-12);

		addFocusListener(this); // Bij tabs / verklikken
		addActionListener(this); // Bij enter
		pModel.addChangeListener(this);
	}

	public void stateChanged(ChangeEvent e) {
		oldValue = scale(pModel.getWaarde(index));
		setText(scale(pModel.getWaarde(index)));
	}

	public void actionPerformed(ActionEvent e) {
		somethingChanged();
	}

	public void focusGained(FocusEvent e) {
		selectAll();
	}

	public void focusLost(FocusEvent e) {
		somethingChanged();
	}

	public void somethingChanged() {
		if (verify(getText())) {
			pModel.setWaarde(rescale(getText()), index);
		} else {
			Logger.getLogger("Elektrobank").setUseParentHandlers(false);
			Logger.getLogger("Elektrobank").addHandler(mBeheerder.getLoggerModel().getLogHandler());
			Logger.getLogger("Elektrobank").log(Level.WARNING, "Wrong value, corrected it to the previous value.");
			JOptionPane.showMessageDialog(null, "Wrong value.", "Warning", JOptionPane.WARNING_MESSAGE);
			setText(oldValue);
		}
	}

	public String scale(double waarde) {
		Format format = new DecimalFormat("#.###");

		int i = 3;
		String[] scales = {"G", "M", "k", "", "m", "µ", "n", "p"};

		if (waarde != 0) {
			if (waarde < 1) {
				while (waarde < 1 && i < scales.length - 1) {
					waarde *= 1000;
					i += 1;
				}
			} else if (waarde >= 1000) {
				while (waarde >= 1000 && i > 0) {
					waarde /= 1000;
					i -= 1;
				}
			}
		}
		return format.format(waarde) + scales[i];
	}

	public double rescale(String waarde) {
		double returnWaarde;
		if (rescaleMap.containsKey(waarde.charAt(waarde.length() - 1))) {
			returnWaarde = Double.parseDouble(waarde.substring(0, waarde.length() - 1)) * rescaleMap.get(waarde.charAt(waarde.length() - 1));
		} else {
			returnWaarde = Double.parseDouble(waarde);
		}
		return returnWaarde;
	}

	public boolean verify(String input) {
		boolean ok = false;
		Matcher matcher;
		String waarde = input;
		Pattern regex = Pattern.compile("^[0-9]*\\.?[0-9]*[GMkmµnp]?$");
		matcher = regex.matcher(waarde);

		if (matcher.matches()) {
			ok = true;
		}

		return ok;
	}
}
