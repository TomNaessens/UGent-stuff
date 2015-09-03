/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */
package elektrobank.Controllers.Logger;

import elektrobank.Models.Logger.LoggerModel;
import java.util.ArrayList;
import java.util.logging.LogRecord;
import javax.swing.DefaultListModel;
import javax.swing.JList;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class ChangeList extends JList implements ChangeListener {

	LoggerModel lModel;
	DefaultListModel listModel;

	public ChangeList(LoggerModel lModel, DefaultListModel listModel) {
		super(listModel);
		lModel.addChangeListener(this);
		this.lModel = lModel;
		this.listModel = listModel;
	}

	public void stateChanged(ChangeEvent e) {
		ArrayList<LogRecord> recordList = lModel.getLogs();
		for (LogRecord record : recordList) {
			if (record.getLevel().intValue() >= lModel.getCurrentLevel().intValue()
				   && lModel.getShowLog().get(record.getLoggerName())) {
				listModel.addElement(record.getLevel() + ": " + record.getMessage() + " (" + record.getLoggerName() + ") ");
			}
		}
		ensureIndexIsVisible(listModel.getSize()-1);
	}
}
