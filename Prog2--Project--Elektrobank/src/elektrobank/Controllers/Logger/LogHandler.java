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
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import javax.swing.DefaultListModel;

public class LogHandler extends Handler {

	LoggerModel lModel;
	DefaultListModel listModel;

	public LogHandler(LoggerModel lModel, DefaultListModel listModel) {
		super.setLevel(Level.ALL);
		this.lModel = lModel;
		this.listModel = listModel;
	}

	@Override
	public void publish(LogRecord record) {

		lModel.addLog(record);

	}

	@Override
	public void flush() {
	}

	@Override
	public void close() throws SecurityException {
	}
}
