package fileInteraction;

import java.io.File;
import java.io.FilenameFilter;
import javax.swing.JFileChooser;
import javax.swing.filechooser.FileNameExtensionFilter;

/**
 * @author NVH @filename BoardGameReader.java
 */
public class BoardGameReader {

	public static final File gameDir = new File(UserFileReader.fileDir.getPath() + "/PeerFunGames");

	public File getBoardGame() {
		File file = null;
		JFileChooser fc = new JFileChooser(gameDir);
		fc.setFileFilter(new FileNameExtensionFilter(".jar", "jar"));
		if (fc.showOpenDialog(fc) == JFileChooser.APPROVE_OPTION) {
			file = fc.getSelectedFile();

			while (file == null) {
				fc = new JFileChooser(gameDir);
				fc.setFileFilter(new FileNameExtensionFilter(".jar", "jar"));
				if (fc.showOpenDialog(fc) == JFileChooser.APPROVE_OPTION) {
					file = fc.getSelectedFile();
				}

			}
		}
		return file;
	}

	public String[] getBoardGames() {

		String[] allFiles = gameDir.list(new FilenameFilter() {

			@Override
			public boolean accept(File dir, String name) {
				return name.endsWith(".jar");
			}
		});

		return allFiles;
	}

	public File getBoardGame(String gameName) {
		File file = new File(gameDir + "/" + gameName + ".jar");
		if (!file.exists()) {
			file = null;
		}
		return file;
	}
}