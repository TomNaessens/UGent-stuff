
package stemmer;

public class VotingProof {

    private String text;
    private String sign;

    public VotingProof(String text, String sign) {
        this.text = text;
        this.sign = sign;
    }

    public String toString() {
        return "Text: " + text + "\nSign: " + sign + "\n";
    }

}
