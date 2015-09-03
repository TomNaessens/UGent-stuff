
package stemmer;

import java.util.Map;
import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;

public class VotingForm {

    private Map<String, List<String>> parties;

    public VotingForm() {
        parties = new HashMap<>();
    }

    public List<String> addParty(String partyname) {
        List<String> party = new ArrayList<>();
        parties.put(partyname, party);
        return party;
    }

    public Map<String, List<String>> getParties() {
        return parties;
    }

    public String toString() {
        StringBuilder result = new StringBuilder();
        for(String party : parties.keySet()) {
            result.append(party);
            result.append(": ");
            result.append(parties.get(party));
            result.append('\n');
        }
        return result.toString();
    }
}
