
package stemmer;

import java.io.IOException;
import java.net.ProtocolException;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.Map;
import java.util.HashMap;

import javax.net.ssl.HttpsURLConnection;

import com.fasterxml.jackson.databind.ObjectMapper;

import stemmer.Vote;
import stemmer.Bijzitter;
import ssl.VotingSSLFactory;

/**
 * @author Felix Van der Jeugt
 * Sources: (apart from those with Bijzitter)
 */
public class Stembus {

    private static final String stem = "https://zeus.ugent.be/overheid/stem";

    public static boolean post(Bijzitter bijzitter, Vote vote) {
        URL url;
        HttpsURLConnection con;
        int responseCode;
        ObjectMapper mapper = new ObjectMapper();
        try {

            // Building vote json
            Map<String, String> jsonmap = new HashMap<>();
            jsonmap.put("id", bijzitter.getAnonymousIdentity());
            jsonmap.putAll(vote.encryptWith(bijzitter.getSymmetricalKey()));

            // Posting the vote.
            url = new URL(stem);
            con = (HttpsURLConnection) url.openConnection();
            con.setSSLSocketFactory(VotingSSLFactory.getStembusFactory());
            con.setRequestProperty("Accept", "application/json");
            con.setRequestMethod("POST");
            con.setDoOutput(true);
            con.getOutputStream().write("request=".getBytes());
            mapper.writeValue(con.getOutputStream(), jsonmap);
            con.getOutputStream().flush();
            responseCode = con.getResponseCode();

        } catch(MalformedURLException e) {
            e.printStackTrace();
        } catch(ProtocolException e) {
            e.printStackTrace();
        } catch(IOException e) {
            e.printStackTrace();
        }
        return true;
    }

}
