package models;

import utils.LangMessages;

public enum Language {
	ENGLISH("en"),
    DUTCH("nl"),
    FRENCH("fr"),
    GERMAN("de");

    // The official code that corresponds to the language
    private String officialCode;

    private Language(String officialCode) {
        this.officialCode = officialCode;
    }

    public String getOfficialCode() {
        return officialCode;
    }

    public static Language getDefault() {
        return ENGLISH;
    }

    /**
     * Custom toString method
     * @return the name of the value in the appropriate language
     */
    @Override
	public String toString(){
		return LangMessages.get("enum.language." + name());
	}

}
