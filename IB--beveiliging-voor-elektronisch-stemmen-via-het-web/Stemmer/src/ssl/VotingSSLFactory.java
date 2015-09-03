
package ssl;

import java.io.IOException;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.security.KeyStore;
import java.security.KeyStoreException;
import java.security.KeyManagementException;
import java.security.NoSuchAlgorithmException;

import java.security.cert.CertificateException;
import javax.net.ssl.TrustManagerFactory;
import javax.net.ssl.SSLSocketFactory;
import javax.net.ssl.SSLContext;


/**
 * @author Felix Van der Jeugt
 * Source:
 * http://stackoverflow.com/questions/859111/how-do-i-accept-a-self-signed-certificate-with-a-java-httpsurlconnection/859271#859271
 */
public class VotingSSLFactory {

    private static SSLSocketFactory bijzitter = null;
    private static SSLSocketFactory stembus = null;

    private static SSLSocketFactory generate(String keyStoreFile) {
        try {
            KeyStore keyStore = KeyStore.getInstance(KeyStore.getDefaultType());
            FileInputStream fis = null;
            try {
                fis = new FileInputStream(keyStoreFile);
                keyStore.load(fis, "felieks".toCharArray()); // our password
            } finally {
                if(fis != null) fis.close();
            }
            TrustManagerFactory tmf = TrustManagerFactory.getInstance(TrustManagerFactory.getDefaultAlgorithm());
            tmf.init(keyStore);
            SSLContext ctx = SSLContext.getInstance("TLS");
            ctx.init(null, tmf.getTrustManagers(), null);
            return ctx.getSocketFactory();
        } catch(KeyStoreException e) {
            e.printStackTrace();
        } catch(FileNotFoundException e) {
            e.printStackTrace();
        } catch(KeyManagementException e) {
            e.printStackTrace();
        } catch(NoSuchAlgorithmException e) {
            e.printStackTrace();
        } catch(IOException e) {
            e.printStackTrace();
        } catch(CertificateException e) {
            e.printStackTrace();
        }
        assert false: "Shouldn't arrive here.";
        return null;
    }

    public static SSLSocketFactory getBijzitterFactory() {
        if(bijzitter == null) bijzitter = generate("certs/bijzitter.jks");
        return bijzitter;
    }

    public static SSLSocketFactory getStembusFactory() {
        if(stembus == null) stembus = generate("certs/stembus.jks");
        return stembus;
    }

}
