/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Models.Logger;

import elektrobank.Controllers.Logger.LogHandler;
import elektrobank.utils.Model;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import javax.swing.DefaultListModel;

public class LoggerModel extends Model {
	private static final Level[] LEVELS = {Level.SEVERE, Level.WARNING, Level.INFO, Level.CONFIG, Level.ALL};

	private ArrayList<LogRecord> logs;
	private Level currentLevel;
	private HashMap<String, Boolean> showLog;
	private DefaultListModel logListModel;
	private LogHandler logHandler;
	

	public LoggerModel(DefaultListModel logListModel) {
		
		this.logListModel = logListModel;

		logHandler = new LogHandler(this, logListModel);

		logs = new ArrayList<LogRecord>();
		currentLevel = Level.ALL; // Initialiseer op alles

		showLog = new HashMap<String, Boolean>();
		showLog.put("Elektrobank", false);
		showLog.put("jOldeSpice", false);
	}

	public void setLevel(Level level) {
		currentLevel = level;
		logListModel.clear();
		fireStateChanged();
	}

	public void setShow(String title, boolean bool) {
		showLog.put(title, (Boolean) bool);
		logListModel.clear();
		fireStateChanged();
	}

	public void addLog(LogRecord log) {
		logs.add(log);
		logListModel.clear();
		fireStateChanged();
	}

	public ArrayList<LogRecord> getLogs() {
		return logs;
	}

	public Level[] getLevels() {
		return LEVELS;
	}

	public Level getCurrentLevel() {
		return currentLevel;
	}

	public HashMap<String, Boolean> getShowLog() {
		return showLog;
	}

	public LogHandler getLogHandler() {
		return logHandler;
	}

}
