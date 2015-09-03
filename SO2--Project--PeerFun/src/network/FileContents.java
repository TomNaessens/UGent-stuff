package network;

import java.io.*;
import java.io.File;
import java.util.ArrayList;

/*
 *  @author Dieter Decaestecker
 *  class : FileContents
 */
public class FileContents implements Serializable
{
    public File file;
    public ByteBuffer fileContents;
    public FileContents(File file) throws FileNotFoundException, IOException
    {
        this.file = file;
        InputStream in = new FileInputStream(file);
        byte [] fileArray  = new byte [(int) file.length()];
        in.read(fileArray,0,fileArray.length);
        fileContents = new ByteBuffer(fileArray);
        in.close();
  }
   
}