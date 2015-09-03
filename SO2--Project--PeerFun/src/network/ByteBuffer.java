package network;
 
import java.io.Serializable;
 
/*
 *  @author Dieter Decaestecker
 *  class : ByteBuffer
 */
public class ByteBuffer implements Serializable
{
    public byte[] byteBuffer;
    public ByteBuffer(byte[] byteBuffer)
    {
        this.byteBuffer = byteBuffer;
    }
}