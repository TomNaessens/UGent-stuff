package utils;

// Uses the ROT13 algorithm to obfuscate a string

public class Obfuscate {

    public static String obfuscate(String original) {
        return rot13(original);
    }

    public static String deObfuscate(String obfuscated) {
        return rot13(obfuscated);
    }

    // Source: http://introcs.cs.princeton.edu/java/31datatype/Rot13.java.html
    private static String rot13(String input) {

        String output = "";

        for (int i = 0; i < input.length(); i++) {
            char c = input.charAt(i);
            if (c >= 'a' && c <= 'm') c += 13;
            else if (c >= 'A' && c <= 'M') c += 13;
            else if (c >= 'n' && c <= 'z') c -= 13;
            else if (c >= 'N' && c <= 'Z') c -= 13;
            output += c;
        }

        return output;

    }

}
