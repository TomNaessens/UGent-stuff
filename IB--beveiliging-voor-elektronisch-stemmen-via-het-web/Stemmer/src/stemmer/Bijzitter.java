
package stemmer;

import java.io.IOException;
import java.net.MalformedURLException;
import java.net.ProtocolException;
import java.net.URL;
import java.util.Map;
import java.util.HashMap;
import java.util.List;
 
import javax.net.ssl.HttpsURLConnection;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.core.type.TypeReference;

import be.belgium.eid.eidlib.BeID;
import be.belgium.eid.eidlib.BeID.SignatureType;
import be.belgium.eid.exceptions.EIDException;
import be.belgium.eid.eidcommon.ByteConverter;

import ssl.VotingSSLFactory;
import stemmer.VotingProof;
import stemmer.Exceptions;

/**
 * @author Felix Van der Jeugt
 * Sources:
 * http://www.mkyong.com/java/how-to-send-http-request-getpost-in-java/
 * http://examples.javacodegeeks.com/core-java/json/jackson/convert-java-map-to-from-json-using-jackson-example/
 * https://github.com/KeejOow/eidlib/tree/master/eidlibsamples/src/be/belgium/eid/samples
 */
public class Bijzitter {

    private static final String letter = "https://zeus.ugent.be/bijzitter/letter";
    private static final String check =  "https://zeus.ugent.be/bijzitter/check";

    private VotingForm form;
    private String anonymousIdentity;
    private byte[] symmetricalKey;
    private String nationalNumber;
    
    // For testing purposes
    public Bijzitter() {
        form = new VotingForm();
    }

    @SuppressWarnings("unchecked") // For json to object conversion
    public Bijzitter(String pin) throws Exceptions.IncorrectPIN, Exceptions.EIDNotFound, Exceptions.RetrievalFailed, Exceptions.DuplicateVote {
        form = null;
        anonymousIdentity = null;
        symmetricalKey = new byte[256];

        ObjectMapper mapper = new ObjectMapper();
        Map<String, Object> jsonmap;
        URL url = null;
        HttpsURLConnection con;
        int responseCode;

        try {
            System.out.println(pin);
            jsonmap = signNationalNumber(pin);

            url = new URL(letter);
            con = (HttpsURLConnection) url.openConnection();
            con.setSSLSocketFactory(VotingSSLFactory.getBijzitterFactory());
            con.setRequestProperty("Accept", "application/json");
            con.setRequestMethod("POST");
            con.setDoOutput(true);
            con.getOutputStream().write("request=".getBytes());
            mapper.writeValue(con.getOutputStream(), jsonmap);
            con.getOutputStream().flush();
            responseCode = con.getResponseCode();

            jsonmap = mapper.readValue(con.getInputStream(), new TypeReference<Map<String, Object>>(){});
            if(jsonmap.containsKey("error")) throw new Exceptions.DuplicateVote();
            anonymousIdentity = (String) jsonmap.get("id");
            symmetricalKey = ByteConverter.unhexify(((String) jsonmap.get("key")).toUpperCase());
            Map<String, List<String>> parties = (Map<String, List<String>>) jsonmap.get("choices");
            form = new VotingForm();
            for(String party : parties.keySet()) {
                List<String> list = form.addParty(party);
                list.addAll(parties.get(party));
            }
        } catch(MalformedURLException | ProtocolException e) {
            assert false: "Should not happen as urls are hardcoded.";
        } catch(IOException e) {
            throw new Exceptions.RetrievalFailed(e);
        }
    }

    public VotingForm getVotingForm() {
        return form;
    }

    public byte[] getSymmetricalKey() {
        return symmetricalKey;
    }

    public String getAnonymousIdentity() {
        return anonymousIdentity;
    }

    private Map<String, Object> signNationalNumber(String pin) throws Exceptions.IncorrectPIN, Exceptions.EIDNotFound {
        Map<String, Object> result = new HashMap<>();
        BeID eID;

        try {
            eID = new BeID(true); //TODO should be false, but that makes getIDData fail.
            System.out.println(); // For some odd reason the program crashes if this is not here...
            nationalNumber = eID.getIDData().getNationalNumber();
        } catch(EIDException e) { throw new Exceptions.EIDNotFound(e); }
        result.put("identity", nationalNumber);

        byte[] signature = new byte[]{0};
        try {
            signature = eID.generateSignature(nationalNumber.getBytes(), pin, SignatureType.AUTHENTICATIONSIG);
        } catch(EIDException e) { throw new Exceptions.IncorrectPIN(pin); }
        result.put("sign", ByteConverter.hexify(signature));

        return result;
    }

    public VotingProof getVotingProof() throws Exceptions.DeliveringFailed {
        ObjectMapper mapper = new ObjectMapper();
        Map<String, String> jsonmap;
        URL url;
        HttpsURLConnection con;
        int responseCode;

        try {
            // making post data
            jsonmap = new HashMap<>();
            jsonmap.put("identity", nationalNumber);
            jsonmap.put("anonymous_identity", anonymousIdentity);

            // posting post data
            url = new URL(check);
            con = (HttpsURLConnection) url.openConnection();
            con.setSSLSocketFactory(VotingSSLFactory.getBijzitterFactory());
            con.setRequestProperty("Accept", "application/json");
            con.setRequestMethod("POST");
            con.setDoOutput(true);
            con.getOutputStream().write("request=".getBytes());
            mapper.writeValue(con.getOutputStream(), jsonmap);
            con.getOutputStream().flush();
            responseCode = con.getResponseCode();

            // parsing response data
            jsonmap = mapper.readValue(con.getInputStream(), new TypeReference<Map<String, String>>(){});
            return new VotingProof(jsonmap.get("brief"), jsonmap.get("sign"));
        } catch(MalformedURLException | ProtocolException e) {
            assert false: "Should not happen as urls are hardcoded.";
        } catch(IOException e) {
            throw new Exceptions.DeliveringFailed(e);
        }

        return null;
            
    }

}
