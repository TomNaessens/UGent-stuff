
package stemmer;

import java.util.List;
import java.util.Map;
import java.util.HashMap;
import java.security.InvalidKeyException;

import java.security.SecureRandom;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.core.JsonProcessingException;

import gnu.crypto.mode.IMode;
import gnu.crypto.mode.ModeFactory;
import gnu.crypto.pad.IPad;
import gnu.crypto.pad.PadFactory;

import be.belgium.eid.eidcommon.ByteConverter;

/**
 * @author Felix Van der Jeugt
 * Sources:
 * http://stackoverflow.com/a/15551591/1626199
 */
public class Vote {

    private static final int IV_SIZE = 16;
    private static final int KEY_SIZE = 32;

    private String party;
    private List<String> preferences;

    public Vote(String party, List<String> preferences) {
        this.party = party;
        this.preferences = preferences;
    }

    public String getParty() {
        return party;
    }

    public List<String> getPreferences() {
        return preferences;
    }

    public String toString() {
        try {
            ObjectMapper mapper = new ObjectMapper();
            Map<String, Object> jsonmap = new HashMap<>();
            jsonmap.put("party", party);
            jsonmap.put("prefs", preferences);
            return mapper.writeValueAsString(jsonmap);
        } catch(JsonProcessingException e) {
            assert false: "Ow come one...";
        }
        return null;
    }

    public Map<String, String> encryptWith(byte[] aesKey) {
        int bs = 16;

        // making the initialisation vector
        SecureRandom secureRandom = new SecureRandom();
        byte[] iv = new byte[bs];
        secureRandom.nextBytes(iv);

        // making the cipher
        IMode cipher = ModeFactory.getInstance("CBC", "AES", 16);
        Map<String, Object> attributes = new HashMap<>();
        attributes.put(IMode.CIPHER_BLOCK_SIZE, new Integer(16));
        attributes.put(IMode.KEY_MATERIAL, aesKey);
        attributes.put(IMode.STATE, new Integer(IMode.ENCRYPTION));
        attributes.put(IMode.IV, iv);
        try {
            cipher.init(attributes);
        } catch(InvalidKeyException e) {
            throw new RuntimeException(e);
        }
        
        // In and buffer and out.
        StringBuilder inString = new StringBuilder(this.toString());
        for(int i = 0; i < bs; i++) inString.append(" "); // lol padding
        byte[] pt = inString.toString().getBytes();
        byte[] bf = new byte[bs]; // buffer
        StringBuilder out = new StringBuilder();

        // Encryption
        for (int i = 0; i + bs < pt.length; i += bs)
        {
                cipher.update(pt, i, bf, 0);
                out.append(ByteConverter.hexify(bf));
        }

        Map<String, String> result = new HashMap<>();
        result.put("iv", ByteConverter.hexify(iv));
        result.put("ciphertext", out.toString());
        return result;
    }

}
