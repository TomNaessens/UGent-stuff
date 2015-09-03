package fileInteraction;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import network.FileContents;

/**
 * @author NVH @filename BoardGameWriter.java
 */
public class BoardGameWriter {

	public static final int BUFFER_SIZE = 512;

	public void saveBoardGame(FileContents jarFile) {
		new File(BoardGameReader.gameDir + "").mkdirs();

		try {

			OutputStream out = new FileOutputStream(jarFile.file);

			out.write(jarFile.fileContents.byteBuffer);

			out.close();
			System.out.println("File copied.");

		} catch (FileNotFoundException ex) {

			System.out.println(ex.getMessage() + " in the specified directory.");
			System.exit(0);

		} catch (IOException e) {

			System.out.println(e.getMessage());
		}

	}

	public void saveBoardGame(File jarFile) {
		(new File(BoardGameReader.gameDir + "")).mkdirs();
		try {
			FileOutputStream fout = new FileOutputStream(BoardGameReader.gameDir + "/" + jarFile.getName());
			InputStream is = new FileInputStream(jarFile);
			long length = jarFile.length();

			byte[] buffer = new byte[BUFFER_SIZE];

			while (true) {
				int nRead = is.read(buffer, 0, buffer.length);
				if (nRead <= 0) {
					break;
				}
				fout.write(buffer, 0, nRead);
			}
			is.close();
			fout.close();
		} catch (IOException ioex) {
			System.out.println("File not found!" + ioex);
		}
	}
}